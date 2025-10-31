#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>

#define ereport(err_msg) \
do { \
	if (errno != 0) perror((err_msg)); \
	else if (printf("%s\n", (err_msg)) < 0) perror("Ereport failed"); \
} while (0)

#define ereport_and_exit(err_msg, return_val) \
do { \
	if (errno != 0) perror((err_msg)); \
	else if (printf("Internal error: %s\n", (err_msg)) < 0) \
		perror("Ereport failed"); \
	return (return_val); \
} while (0)

typedef struct Literal
{
	unsigned char	name;
	char			assigned_value;
	bool			is_negated;

	/*
	 * Stack depth is assigned when we get rid of this literal during clause
	 * simplification.
	 */
	unsigned char	stack_depth;
}		Literal;

/* List values that can be assigned to a literal. */
#define VAL_FALSE		0
#define	VAL_TRUE		1
/* Special value for literal, for which we did not assign any value. */
#define	VAL_UNASSIGNED	-1

#define LiteralGivesTrue(literal_ptr) \
	(((literal_ptr)->assigned_value == VAL_FALSE && \
	  (literal_ptr)->is_negated) || \
	 ((literal_ptr)->assigned_value == VAL_TRUE && \
	  !(literal_ptr)->is_negated))

#define InvalidLiteralName	0

/*
 * We assume that there cannot be more than 150 variables. Thus, CHAR_MAX
 * value can be occupied by a flag.
 */
#define InvalidStackDepth	255

#define LiteralIsInUse(literal_ptr) \
	((literal_ptr)->stack_depth == InvalidStackDepth || \
	 (literal_ptr)->name == InvalidLiteralName)

#define LiteralSetUnused(literal_ptr, stack_depth) \
do { \
	(literal_ptr)->stack_depth = (stack_depth); \
} while (0)

#define LiteralSetUsed(literal_ptr) \
do { \
	(literal_ptr)->stack_depth = (InvalidStackDepth); \
} while (0)

typedef struct Clause
{
	Literal		*literals;
	/* Number of literals that are actually in the clause */
	int			n_in_use;
}		Clause;

typedef struct Formula
{
	/* List of all clauses within formula */
	Clause		*clauses;

	/*
	 * We don't want to call 'malloc' for each clause. So, we allocating memory
	 * for literals and their values as a one big chuck. Thus, pointers in
	 * Clause struct are only points to different places off arrays below.
	 */
	Literal		*literals;

	int				nclauses;
	int				nlit_total;
}		Formula;

#define	VAL_PROPAGATION		1
#define UNIT_PROPAGATION	2
typedef struct Assignment
{
	unsigned char	literal_name;
	char			oldval;
	char			newval;
	unsigned char	a_type; /* type of an assignment */
	unsigned char	stack_depth;
}		Assignment;

typedef struct AssignmentStack
{
	Assignment		*data;
	unsigned char	depth;
	unsigned char	capacity;
}		AssignmentStack;

#define STACK_MAX_CAPACITY	255

static int lits_per_clause = 0;

static void
push(AssignmentStack *stack, Assignment *s)
{
	s->stack_depth = (stack->depth + 1);

	if (stack->depth >= stack->capacity)
	{
		ereport("Assignment stack overflow");
		exit(1);
	}

	stack->data[stack->depth++] = *s;
}

Assignment pop(AssignmentStack *stack) {
	return stack->data[--stack->depth];
}

static bool
stack_is_empty(AssignmentStack *stack)
{
	return stack->depth == 0;
}

static void
revert_change(Formula *formula, Assignment a)
{
	for (int i = 0; i < formula->nlit_total; i++)
	{
		Literal *l = &formula->literals[i];

		if (l->stack_depth != a.stack_depth)
			continue;

		if (!LiteralIsInUse(l))
		{
			LiteralSetUsed(l);
			formula->clauses[i / lits_per_clause].n_in_use += 1;
		}

		if (l->name == a.literal_name)
			l->assigned_value = a.oldval;
	}
}

// TODO delete it
static void
print_formula(Formula *f, char *additional_str)
{
	if (additional_str != NULL)
		printf("%s\n", additional_str);

	for (int i = 0; i < f->nclauses; i++)
	{
		Clause *cl = &f->clauses[i];
		for (int j = 0; j < lits_per_clause; j++)
		{
			if (!LiteralIsInUse(&cl->literals[j]))
				continue;

			printf("%s%d %s",
					cl->literals[j].is_negated ? "NOT " : "",
					cl->literals[j].name,
					j == lits_per_clause - 1 ? "\n" : "OR ");
		}
		// printf(" (in use %d)\n", cl->n_in_use);
	}

	printf("============\n\n");
}

/*
 * Returns non-zero value iff single line was readed.
 */
static int
readline(FILE *file)
{
	char	next_symb = 'c';

	while (next_symb != '\n' && next_symb != EOF)
		next_symb = fgetc(file);

	/* Error occured */
	if (next_symb == EOF)
		return 0;

	return 1;
}

/*
 * Files in DIMACS format may contain comments - lines beginning with 'c'
 * literal. This function will skip them.
 *
 * Function returns non-zero value iff comments are skipped successfully.
 */
static int
skip_comments(FILE *file)
{
	char	next_symb = 'c';
	int		rc;

	if (file == NULL)
		ereport_and_exit("Invalid argument: file is NULL", 0);

	while (!feof(file) && next_symb != 'p')
	{
		if ((next_symb = fgetc(file)) == EOF)
			ereport_and_exit("Cannot read from file", 0);

		if (next_symb == 'c')
		{
			/*
			 * Skip the line with a comment. We are expecting that whole line
			 * is present, so exit if we cannot read it.
			 */
			if (!readline(file))
				ereport_and_exit("Cannot read from file", 0);

			continue;
		}
		else if (next_symb != 'p')
		{
			/*
			 * We are expecting only 'c' or 'p' literal at the beginning of
			 * the line.
			 */
			ereport_and_exit("Invalid file format", 0);
		}
	}

	/*
	 * Step back, so certain position in the file will point to the start of
	 * config line.
	 */
	if (fseek(file, -1, SEEK_CUR) != 0)
		ereport_and_exit("Cannot fseek in file", 0);

	return 1;
}

static int
find_nlit_per_clause(FILE *file)
{
	fpos_t	current_pos;
	int val;
	int	nvars = 0;

	if (fgetpos(file, &current_pos) < 0)
		ereport_and_exit("Cannot read file", 0);

	while (true)
	{
		int rc = fscanf(file, "%d", &val);
		nvars++;

		/* EOF or some another delimeter encountered */
		if (feof(file) || val == 0 || rc != 1)
			break;
	}

	if (fsetpos(file, &current_pos) < 0)
		ereport_and_exit("Cannot read file", 0);

	return --nvars;
}

/*
 * Read next value from DIMACS-formatted file.
 * Reutns 0 on eof, 1 on success.
 */
static int
read_next_val(FILE *file, int *val)
{
	while (true)
	{
		int rc = fscanf(file, "%d", val);

		/* EOF or some another delimeter encountered */
		if (feof(file) || rc != 1)
			return 2;
		else if (*val == 0)
			continue;
		/* All good - we read the value */
		else
			break;
	}

	return 1;
}

static void
delete_clause_from_formula(Formula *formula, Clause *clause,
						   unsigned char stack_depth)
{
	for (int i = 0; i < lits_per_clause; i++)
	{
		if (LiteralIsInUse(&clause->literals[i]))
			LiteralSetUnused(&clause->literals[i], stack_depth);
	}

	clause->n_in_use = 0;
}

static bool
clause_is_empty(Clause *cl, int nliterals)
{
	bool	all_unused = true;

	for (int i = 0; i < nliterals; i++)
	{
		if (!LiteralIsInUse(&cl->literals[i]))
			continue;

		all_unused = false;

		if (cl->literals[i].assigned_value == VAL_UNASSIGNED)
			return false;

		if (LiteralGivesTrue(&cl->literals[i]))
			return false;
	}

	return all_unused ? false : true;
}

/*
 * Returns false iff we found the polar pair.
 */
static bool
unit_propagate(Formula *formula, unsigned char stack_depth)
{
	unsigned char target_literal_name;
	bool	value_to_assign;

retry:
	target_literal_name = InvalidLiteralName;

	/* Try to find clause, that contains only single literal */
	for (int i = 0; i < formula->nclauses; i++)
	{
		Clause *unit_clause = &formula->clauses[i];

		if (unit_clause->n_in_use != 1)
			continue;

		/* Found one */

		/* Find exact literal and creaete value for it */
		for (int j = 0; j < lits_per_clause; j++)
		{
			Literal	*literal = &unit_clause->literals[j];

			if (!LiteralIsInUse(literal))
				continue;

			target_literal_name = literal->name;
			value_to_assign = !(literal->is_negated);

			// LiteralSetUnused(literal, stack_depth);
			// unit_clause->n_in_use = 0;
		}
		break;
	}

	if (target_literal_name == InvalidLiteralName)
		return true;

	for (int i = 0; i < formula->nclauses; i++)
	{
		Clause *cl;

		if (formula->clauses[i].n_in_use == 0)
			continue;

		cl = &formula->clauses[i];

		for (int j = 0; j < lits_per_clause; j++)
		{
			if (cl->literals[j].name != target_literal_name ||
				!LiteralIsInUse(&cl->literals[j]))
			{
				/*
				 * Skip not matched literals and literals that are not actually
				 * in the clause.
				 */
				continue;
			}

			cl->literals[j].assigned_value = value_to_assign;

			if (LiteralGivesTrue(&cl->literals[j]))
				delete_clause_from_formula(formula, cl, stack_depth);
			else if (clause_is_empty(cl, lits_per_clause))
			{
				/* Delete literal from clause */
				LiteralSetUnused(&cl->literals[j], stack_depth);
				// printf("set %d unused with depth %d (propagate unit)\n",
				// 	cl->literals[j].name, stack_depth);
				cl->n_in_use -= 1;
				return false; // TODO может не стоит досрочно возвращаться отсюда?
			}
			else
			{
				/* Delete literal from clause */
				LiteralSetUnused(&cl->literals[j], stack_depth);
				// printf("set %d unused with depth %d (propagate unit)\n",
				// 	cl->literals[j].name, stack_depth);
				cl->n_in_use -= 1;
			}
		}
	}

	goto retry;

	/* Keep compiler quiet */
	return true;
}

static unsigned char
find_unassigned_literal(Formula *formula)
{
	unsigned char lname = InvalidLiteralName;

	for (int i = 0; i < formula->nlit_total; i++)
	{
		if (!LiteralIsInUse(&formula->literals[i]))
			continue;

		if (formula->literals[i].assigned_value == VAL_UNASSIGNED)
		{
			lname = formula->literals[i].name;
			break;
		}
	}

	return lname;
}

/*
 * Returns 'false' iff any empty clause appeared after assign.
 */
static bool
propagate_literal_value(Formula *formula, unsigned char literal_name,
						char newvalue, unsigned char stack_depth)
{
	for (int i = 0; i < formula->nlit_total; i++)
	{
		Clause	*c;

		if (formula->literals[i].name != literal_name ||
			!LiteralIsInUse(&formula->literals[i]))
		{
			/*
			 * Skip not matched literals and literals that are not actually
			 * in the clause.
			 */
			continue;
		}

		formula->literals[i].assigned_value = newvalue;
		c = &formula->clauses[i / lits_per_clause];

		if (LiteralGivesTrue(&formula->literals[i]))
			delete_clause_from_formula(formula, c, stack_depth);
		else if (clause_is_empty(c, lits_per_clause))
		{
			/* Delete literal from clause */
			LiteralSetUnused(&formula->literals[i], stack_depth);
			// printf("set %d unused with depth %d (propagate literal)\n",
			// 	formula->literals[i].name, stack_depth);
			c->n_in_use -= 1;
			return false;
		}
		else
		{
			/* Delete literal from clause */
			LiteralSetUnused(&formula->literals[i], stack_depth);
			// printf("set %d unused with depth %d (propagate literal)\n",
			// 	formula->literals[i].name, stack_depth);
			c->n_in_use -= 1;
		}
	}

	return true;
}

static void
drop_formula(Formula *formula)
{
	if (formula == NULL)
		return;

	if (formula->clauses != NULL)
		free(formula->clauses);

	if (formula->literals != NULL)
		free(formula->literals);

	free(formula);
}

static Formula *
create_formula(FILE *file, int nclauses, int nvariables)
{
	Formula *formula;
	int		nlit_per_clause; /* # of literals per clause */
	int		nlit_total; /* total # of literals in formula */

	if ((nlit_per_clause = find_nlit_per_clause(file)) == 0)
		ereport_and_exit("Invalid file format", 0);

	nlit_total = nlit_per_clause * nclauses;

	if ((formula = (Formula *) malloc(sizeof(Formula))) == NULL)
		ereport_and_exit("Cannot allocate memory for Formula", NULL);

	if ((formula->clauses = (Clause *)
			malloc(sizeof(Clause) * nclauses)) == NULL)
	{
		drop_formula(formula);
		ereport_and_exit("Cannot allocate memory for Clauses", NULL);
	}

	if ((formula->literals = (Literal *)
			malloc(sizeof(Literal) * nlit_total)) == NULL)
	{
		drop_formula(formula);
		ereport_and_exit("Cannot allocate memory for literals", NULL);
	}

	/* Fill remaining fields */
	formula->nclauses = nclauses;
	lits_per_clause = nlit_per_clause;
	formula->nlit_total = nlit_total;

	return formula;
}

static int
dpll(FILE *file, int nclauses, int nvariables)
{
	int		val;
	int		rc;
	int		i = 0;
	Formula	*formula;
	AssignmentStack stack = {
		.capacity = STACK_MAX_CAPACITY,
		.depth = 0,
		.data = NULL
	};

	if ((formula = create_formula(file, nclauses, nvariables)) == NULL)
		return 0; /* Error message already emited */

	if ((stack.data = (Assignment *)
			malloc(sizeof(Assignment) * STACK_MAX_CAPACITY)) == NULL)
	{
		drop_formula(formula);
		ereport_and_exit("Cannot allocate memory for assignment stack", 0);
	}

	while ((rc = read_next_val(file, &val)) == 1)
	{
		Literal		l = {
			.name			= val > 0 ? val : val * (-1),
			.is_negated		= (val < 0),
			.stack_depth	= InvalidStackDepth,
			.assigned_value = VAL_UNASSIGNED,
		};

		if (val > nvariables)
		{
			ereport("Invalid file format");
			goto exit;
		}

		formula->literals[i] = l;

		if ((i % lits_per_clause) == 0)
		{
			int clause_idx = i / lits_per_clause;
			formula->clauses[clause_idx].literals = &formula->literals[i];
			formula->clauses[clause_idx].n_in_use = lits_per_clause;
		}

		i++;
	}

	while (true)
	{
		unsigned char next_literal;
		Assignment a;

		print_formula(formula, "cycle head");

		a.literal_name = find_unassigned_literal(formula);

		if (a.literal_name == InvalidLiteralName)
		{
			printf("SAT\n");
			break;
		}

		a.oldval = VAL_UNASSIGNED;
		a.newval = VAL_TRUE;
		push(&stack, &a);

		if (propagate_literal_value(formula, a.literal_name, a.newval, a.stack_depth))
		{
			print_formula(formula, "true val works 1");
			if (unit_propagate(formula, a.stack_depth))
			{
				print_formula(formula, "true val works 2");
				continue;
			}
		}

		print_formula(formula, "true val didnt work");

		a = pop(&stack);

		revert_change(formula, a);
		print_formula(formula, "reverted");

retry:
		a.oldval = VAL_TRUE;
		a.newval = VAL_FALSE;
		push(&stack, &a);

		if (propagate_literal_value(formula, a.literal_name, a.newval, a.stack_depth))
		{
			print_formula(formula, "false val works 1");
			if (unit_propagate(formula, a.stack_depth))
			{
				print_formula(formula, "false val works 2");
				continue;
			}
		}

		print_formula(formula, "false val didnt work");

		do
		{
			if (stack_is_empty(&stack))
				break;

			a = pop(&stack);
			revert_change(formula, a);
			print_formula(formula, "reverted in cycle");
		} while (a.newval == VAL_FALSE);

		if (stack_is_empty(&stack))
		{
			if (a.newval == VAL_TRUE)
				goto retry;

			print_formula(formula, NULL);
			printf("UNSAT\n");
			break;
		}

		goto retry;
	}

exit:
	drop_formula(formula);
	free(stack.data);

	return 1;
}

int main(int argc, char **argv)
{
	FILE			*file = NULL;
	int				nclauses = 0;
	int				ndisjunctions = 0;
	int				nvariables = 0;
	int				victim_idx = 0;

	if (argc != 2)
		ereport_and_exit("Invalid arguments number", -1);

	file = fopen(argv[1], "rb");
	if (file == NULL)
		ereport_and_exit("Cannot open file", -1);

	if (!skip_comments(file))
		return -1; /* Error message is already emited */

	if (fscanf(file, "p cnf %d %d", &nvariables, &ndisjunctions) != 2)
		ereport_and_exit("Cannot read configuration from file - wrong format", -1);

	if (nvariables > 254)
		ereport_and_exit("Too many variables", -1);

	if (!dpll(file, ndisjunctions, nvariables))
		return -1; /* Error message is already emited */

	return 0;
}
