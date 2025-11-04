#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>
#include <limits.h>

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

typedef enum AssignedValue
{
	VAL_UNASSIGNED = -1,
	VAL_FALSE = 0,
	VAL_TRUE = 1,
}		AssignedValue;

typedef struct Clause Clause;

typedef struct Variable
{
	unsigned int name;
	AssignedValue	assigned_value;
	unsigned int	nrelated_clauses;
	Clause 			**related_clauses;
}		Variable;

typedef struct Literal
{
	Variable		*variable;
	bool			is_negated;
	unsigned int	stack_depth;
}		Literal;

#define LiteralGivesTrue(literal_ptr) \
	(((literal_ptr)->variable->assigned_value == VAL_FALSE && \
	  (literal_ptr)->is_negated) || \
	 ((literal_ptr)->variable->assigned_value == VAL_TRUE && \
	  !(literal_ptr)->is_negated))

#define InvalidLiteralName	0

/*
 * We assume that there cannot be more than 150 variables. Thus, CHAR_MAX
 * value can be occupied by a flag.
 */
#define InvalidStackDepth	UINT_MAX

#define LiteralIsInUse(literal_ptr) \
	((literal_ptr)->stack_depth == InvalidStackDepth || \
	 (literal_ptr)->variable->name == InvalidLiteralName)

#define LiteralSetUnused(literal_ptr, stack_d) \
do { \
	(literal_ptr)->stack_depth = (stack_d); \
} while (0)

#define LiteralSetUsed(literal_ptr) \
do { \
	(literal_ptr)->stack_depth = (InvalidStackDepth); \
} while (0)

typedef struct Clause
{
	Literal		*literals;
	int			n_literals;
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
	Variable		*variables;

	int				nclauses;
	int				nvariables;
	int				nliterals_total;
}		Formula;

static void
drop_formula(Formula *formula)
{
	if (formula == NULL)
		return;

	if (formula->clauses != NULL)
		free(formula->clauses);

	if (formula->variables != NULL)
		free(formula->variables);

	// TODO add all appropriate memory free
	// if (formula->assigned_values != NULL)
	// 	free(formula->assigned_values);

	free(formula);
}

static void
add_related_clause(Clause *c, Variable *v)
{
	if (v->related_clauses == NULL)
		v->related_clauses = (Clause **) malloc(sizeof(Clause *));
	else
		v->related_clauses = (Clause **)
			realloc(v->related_clauses,
					sizeof(Clause *) * (v->nrelated_clauses + 1));

	if (v->related_clauses == NULL)
	{
		printf("cannot allocate memory for related clauses\n");
		exit(1);
	}

	v->related_clauses[v->nrelated_clauses] = c;
	v->nrelated_clauses += 1;
}

static void
add_related_literal(Clause *c, Literal l)
{
	if (c->literals == NULL)
		c->literals = (Literal *) malloc(sizeof(Literal));
	else
		c->literals = (Literal *)
			realloc(c->literals, sizeof(Literal) * (c->n_literals + 1));

	if (c->literals == NULL)
	{
		printf("cannot allocate memory for related literals\n");
		exit(1);
	}

	c->literals[c->n_literals] = l;
	c->n_literals += 1;
	c->n_in_use += 1;
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
			return 0;
		/* All good - we read the value */
		else
			break;
	}

	return 1;
}

static void
print_formula(Formula *f, char *additional_str)
{
	// if (additional_str != NULL)
	// 	printf("%s\n", additional_str);

	// for (int i = 0; i < f->nclauses; i++)
	// {
	// 	Clause *c = &f->clauses[i];
	// 	for (int j = 0; j < c->n_literals; j++)
	// 	{
	// 		Literal *l = &c->literals[j];
	// 		if (!LiteralIsInUse(l))
	// 			continue;
	// 		printf("%s%d%s",
	// 			l->is_negated ? "NOT " : "",
	// 			l->variable->name,
	// 			j == c->n_literals - 1 ? "" : " OR ");
	// 	}
	// 	printf("\n");
	// }
	// printf("=============\n");
}



static Formula *
create_formula(FILE *file, int nclauses, int nvariables)
{
	Formula *formula;
	Clause *c;
	int		rc;
	int val;
	unsigned int current_clause = 0;

	if ((formula = (Formula *) malloc(sizeof(Formula))) == NULL)
		ereport_and_exit("Cannot allocate memory for Formula", NULL);

	if ((formula->clauses = (Clause *)
			malloc(sizeof(Clause) * nclauses)) == NULL)
	{
		drop_formula(formula);
		ereport_and_exit("Cannot allocate memory for Clauses", NULL);
	}

	for (int i = 0; i < nclauses; i++)
	{
		Clause c = {
			.literals = NULL,
			.n_literals = 0,
			.n_in_use = 0,
		};
		formula->clauses[i] = c;
	}

	if ((formula->variables = (Variable *)
			malloc(sizeof(Variable) * nvariables)) == NULL)
	{
		drop_formula(formula);
		ereport_and_exit("Cannot allocate memory for literals", NULL);
	}

	for (unsigned int i = 0; i < nvariables; i++)
	{
		Variable v = {
			.assigned_value = VAL_UNASSIGNED,
			.name = i + 1,
			.nrelated_clauses = 0,
			.related_clauses = NULL,
		};
		formula->variables[i] = v;
	}

	/* Fill remaining fields */
	formula->nclauses = nclauses;
	formula->nvariables = nvariables;

	c = &formula->clauses[current_clause];

	while ((rc = read_next_val(file, &val)) == 1)
	{
		unsigned int lname = val > 0 ? val : val * (-1);
		Literal l = {
			.variable = &formula->variables[lname - 1],
			.is_negated = (val < 0),
			.stack_depth = InvalidStackDepth,
		};

		if (val == 0)
		{
			if (++current_clause >= nclauses)
				break;

			c = &formula->clauses[current_clause];
			continue;
		}

		add_related_clause(c, l.variable);
		add_related_literal(c, l);
	}

	return formula;
}

typedef enum AssignmentType
{
	VAL_PROPAGATION = 1,
	UNIT_PROPAGATION = 2,
}		AssignmentType;

typedef struct Assignment
{
	AssignedValue	oldval;
	AssignedValue	newval;
	AssignmentType	type; /* type of an assignment */
	unsigned int	literal_name;
	unsigned int	stack_depth;
}		Assignment;

typedef struct AssignmentStack
{
	Assignment		*data;
	unsigned int	depth;
	unsigned int	capacity;
}		AssignmentStack;

#define STACK_MAX_CAPACITY	1000

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

Assignment
peek(AssignmentStack *stack)
{
	unsigned int depth = (stack->depth - 1);
	return stack->data[depth];
}

Assignment
pop(AssignmentStack *stack)
{
	return stack->data[--stack->depth];
}

static bool
stack_is_empty(AssignmentStack *stack)
{
	return stack->depth == 0;
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

static void
revert_change(Formula *formula, Assignment a)
{
	Variable *v = &formula->variables[a.literal_name - 1];

	for (int i = 0; i < v->nrelated_clauses; i++)
	{
		Clause *c = v->related_clauses[i];
		for (int j = 0; j < c->n_literals; j++)
		{
			Literal *l = &c->literals[j];

			if (l->stack_depth != a.stack_depth)
				continue;

			if (!LiteralIsInUse(l))
			{
				LiteralSetUsed(l);
				c->n_in_use += 1;
			}

			if (l->variable->name == a.literal_name)
				l->variable->assigned_value = a.oldval;
		}
	}
}

static void
delete_clause_from_formula(Formula *formula, Clause *clause,
						   unsigned int stack_depth)
{
	for (int i = 0; i < clause->n_literals; i++)
	{
		if (LiteralIsInUse(&clause->literals[i]))
			LiteralSetUnused(&clause->literals[i], stack_depth);
	}

	clause->n_in_use = 0;
}

static bool
clause_gives_false(Clause *cl)
{
	bool	all_unused = true;

	for (int i = 0; i < cl->n_literals; i++)
	{
		if (!LiteralIsInUse(&cl->literals[i]))
			continue;

		all_unused = false;

		if (cl->literals[i].variable->assigned_value == VAL_UNASSIGNED)
			return false;

		if (LiteralGivesTrue(&cl->literals[i]))
			return false;
	}

	return all_unused ? false : true;
}

static bool propagate_literal_value(Formula *formula, Assignment a);

/*
 * Returns false iff we found the polar pair.
 */
static bool
unit_propagate(Formula *formula, AssignmentStack *stack)
{
	unsigned int target_literal_name;
	bool	value_to_assign;
	bool	no_empty_clauses = true;
	Assignment a;

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
		for (int j = 0; j < unit_clause->n_literals; j++)
		{
			Literal	*literal = &unit_clause->literals[j];

			if (!LiteralIsInUse(literal))
				continue;

			target_literal_name = literal->variable->name;
			value_to_assign = !(literal->is_negated);
			break;
		}

		if (target_literal_name != InvalidLiteralName)
			break;
	}

	if (target_literal_name == InvalidLiteralName)
		return no_empty_clauses;

	a.type = UNIT_PROPAGATION;
	a.oldval = VAL_UNASSIGNED;
	a.newval = value_to_assign;
	a.literal_name = target_literal_name;
	push(stack, &a);

	if (!propagate_literal_value(formula, a))
		no_empty_clauses = false;

	goto retry;

	/* Keep compiler quiet */
	return true;
}

static unsigned int
find_unassigned_literal(Formula *formula)
{
	unsigned int lname = InvalidLiteralName;

	for (int i = 0; i < formula->nvariables; i++)
	{
		if (formula->variables[i].assigned_value == VAL_UNASSIGNED)
		{
			lname = formula->variables[i].name;
			break;
		}
	}

	return lname;
}

/*
 * Returns 'false' iff any empty clause appeared after assign.
 */
static bool
propagate_literal_value(Formula *formula, Assignment a)
{
	Variable *v = &formula->variables[a.literal_name - 1];
	v->assigned_value = a.newval;
	bool	no_empty_clause = true;

	for (int i = 0; i < v->nrelated_clauses; i++)
	{
		Clause *c = v->related_clauses[i];
		for (int j = 0; j < c->n_literals; j++)
		{
			if (c->literals[j].variable->name != a.literal_name)
				continue;

			if (!LiteralIsInUse(&c->literals[j]))
				continue;

			if (LiteralGivesTrue(&c->literals[j]))
				delete_clause_from_formula(formula, c, a.stack_depth);
			else
			{
				if (clause_gives_false(c))
					no_empty_clause = false;
				LiteralSetUnused(&c->literals[j], a.stack_depth);
				c->n_in_use -= 1;
			}
		}
	}

	return no_empty_clause;
}


static Assignment
revert_literal_propagation(Formula *formula, AssignmentStack *stack)
{
	Assignment a;

	/* Revert unit propagations */
	while (true)
	{
		a = peek(stack);

		if (a.type != UNIT_PROPAGATION)
			break;

		a = pop(stack);
		revert_change(formula, a);
	}

	a = pop(stack);

	if (a.type != VAL_PROPAGATION)
	{
		printf("Invalid assignment type in literal propagation reverting\n");
		exit(1);
	}

	revert_change(formula, a);

	return a;
}

static int
dpll(FILE *file, int nclauses, int nvariables)
{
	int		val;
	int		rc;
	int		i = 0;
	Formula	*formula;
	int		cc = 0; /* current clause that is constructed */
	int		nlits_in_clause = 0;
	bool	init_clause = true;
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


	while (true)
	{
		unsigned int next_literal;
		Assignment a;

		a.literal_name = find_unassigned_literal(formula);
		if (a.literal_name == InvalidLiteralName)
		{
			printf("SAT\n");
			break;
		}

		print_formula(formula, "cycle head");

		a.oldval = VAL_UNASSIGNED;
		a.newval = VAL_TRUE;
		a.type = VAL_PROPAGATION;
		push(&stack, &a);

		if (propagate_literal_value(formula, a))
		{
			print_formula(formula, "true val works 1");
			if (unit_propagate(formula, &stack))
			{
				print_formula(formula, "true val works 2");
				continue;
			}
		}

		a = revert_literal_propagation(formula, &stack);
		print_formula(formula, "revert");

retry:
		a.oldval = VAL_UNASSIGNED;
		a.newval = VAL_FALSE;
		a.type = VAL_PROPAGATION;
		push(&stack, &a);

		if (propagate_literal_value(formula, a))
		{
			print_formula(formula, "false val works 1");
			if (unit_propagate(formula, &stack))
			{
				print_formula(formula, "false val works 2");
				continue;
			}
		}

		a = revert_literal_propagation(formula, &stack);
		print_formula(formula, "revert");

		do
		{
			if (stack_is_empty(&stack))
				break;

			a = revert_literal_propagation(formula, &stack);
			print_formula(formula, "revert in cycle");
		} while (a.newval == VAL_FALSE);

		if (stack_is_empty(&stack))
		{
			if (a.newval == VAL_TRUE)
				goto retry;

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

	if (nvariables > 10000)
		ereport_and_exit("Too many variables", -1);

	if (!dpll(file, ndisjunctions, nvariables))
		return -1; /* Error message is already emited */

	return 0;
}
