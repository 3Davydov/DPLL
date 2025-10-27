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

typedef enum LiteralStatus
{
	LIT_UNDEF = -1, /* literal is not present in clause */
	LIT_NEG = 0, /* literal is included into clause with negation */
	LIT_POS = 1, /* literal is included into clause without negation */
}		LiteralStatus;

typedef struct Clause
{
	/* List of literal's names (aka associated numbers) */
	unsigned char	*literals;
	/* List of literal's states - undef/with negation/without negation */
	LiteralStatus	*states;
	/* Number of literal that are actually in the clause */
	int				n_defined;
}		Clause;

typedef struct Formula
{
	/* List of all clauses within formula */
	Clause			*clauses;

	/*
	 * We don't want to call 'malloc' for each clause. So, we allocating memory
	 * for literals and their values as a one big chuck. Thus, pointers in
	 * Clause struct are only points to different places off arrays below.
	 */
	unsigned char	*all_literals;
	LiteralStatus	*all_statuses;

	int				nclauses;
	int				nlit_per_clause; // TODO может, эту переменную стоит занести в сам Clause
	int				nlit_total;
}		Formula;

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
		/* End of line marker encontered - read val from next line */
		else if (*val == 0)
			continue;
		/* All good - we read the value */
		else
			break;
	}

	return 1;
}

static void
delete_clause_from_formula(Formula *formula, Clause *clause)
{
	for (int i = 0; i < formula->nlit_per_clause; i++)
		clause->states[i] = LIT_UNDEF;

	clause->n_defined = 0;
}

static void
delete_lit_from_clause(Clause *clause, int lit_idx)
{
	clause->states[lit_idx] = LIT_UNDEF;
	clause->n_defined -= 1;
}

static int
unit_propagate(Formula *formula)
{
	Clause *target_unit = NULL;
	unsigned char	target_literal;
	bool			value_to_assign;

	/* Try to find clause, that contains only single literal */
	for (int i = 0; i < formula->nclauses; i++)
	{
		if (formula->clauses[i].n_defined != 1)
			continue;

		/* Found one */
		target_unit = &formula->clauses[i];

		/* Find exact literal and creaete value for it */
		for (int j = 0; j < formula->nlit_per_clause; j++)
		{
			if (target_unit->states[j] == LIT_UNDEF)
				continue;

			target_literal = target_unit->literals[j];
			value_to_assign = (target_unit->states[j] == LIT_POS);

			target_unit->states[j] = LIT_UNDEF;
			target_unit->n_defined = 0;
		}
		break;
	}


	if (target_unit == NULL)
	{
		printf("did not found single literal\n");
		return 0;
	}

	printf("found single literal %d\n", target_literal);

	for (int i = 0; i < formula->nclauses; i++)
	{
		Clause *cl;

		if (formula->clauses[i].n_defined == 0)
			continue;

		cl = &formula->clauses[i];
		for (int j = 0; j < formula->nlit_per_clause; j++)
		{
			if (cl->literals[j] != target_literal)
				continue;

			switch (cl->states[j])
			{
				case LIT_POS:
					if (value_to_assign == true)
						delete_clause_from_formula(formula, cl);
					else
						delete_lit_from_clause(cl, j);
					break;
				case LIT_NEG:
					if (value_to_assign == false)
						delete_clause_from_formula(formula, cl);
					else
						delete_lit_from_clause(cl, j);
					break;
				default:
					break;
			}

			/* Nothing left to do */
			break;
		}
	}

	return 1;
}

// TODO довести до ума и учесть все поля
static void
delete_formula(Formula *formula)
{
	if (formula == NULL)
		return;

	if (formula->all_statuses != NULL)
		free(formula->all_statuses);

	if (formula->all_literals != NULL)
		free(formula->all_literals);

	if (formula->clauses != NULL)
		free(formula->clauses);

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
		delete_formula(formula);
		ereport_and_exit("Cannot allocate memory for Clauses", NULL);
	}

	if ((formula->all_literals = (unsigned char *)
			malloc(sizeof(char) * nlit_total)) == NULL)
	{
		delete_formula(formula);
		ereport_and_exit("Cannot allocate memory for literals", NULL);
	}

	if ((formula->all_statuses = (LiteralStatus *)
			malloc(sizeof(LiteralStatus) * nlit_total)) == NULL)
	{
		delete_formula(formula);
		ereport_and_exit("Cannot allocate memory for literal statuses", NULL);
	}

	/* Fill remaining fields */
	formula->nclauses = nclauses;
	formula->nlit_per_clause = nlit_per_clause;
	formula->nlit_total = nlit_total;

	return formula;
}

static int
dpll(FILE *file, int nclauses, int nvariables)
{
	int		val;
	int		rc;
	int		i = 0;
	int		ret_code = 0;
	Formula	*formula;

	if ((formula = create_formula(file, nclauses, nvariables)) == NULL)
		return 0; /* Error message already emited */

	while ((rc = read_next_val(file, &val)) == 1)
	{
		if (val > nvariables)
		{
			ereport("Invalid file format");
			goto exit;
		}

		formula->all_literals[i] = (val > 0) ? val : (val * (-1));
		formula->all_statuses[i] = (val > 0) ? LIT_POS : LIT_NEG;

		if ((i / formula->nlit_per_clause) == 0)
		{
			formula->clauses[i].literals = &formula->all_literals[i];
			formula->clauses[i].states = &formula->all_statuses[i];
			formula->clauses[i].n_defined = formula->nlit_per_clause;
		}

		printf("value %d for literal %d within %d\n", formula->all_statuses[i],
			formula->all_literals[i], i / formula->nlit_per_clause);

		i++;
	}

	unit_propagate(formula);

	ret_code = 1; /* Success */

// TODO везде все очистить
exit:
	delete_formula(formula);

	return ret_code;
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

	if (nvariables > 255)
		ereport_and_exit("Too many variables", -1);

	if (!dpll(file, ndisjunctions, nvariables))
		return -1; /* Error message is already emited */

	return 0;
}
