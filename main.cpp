#include <iostream>
#include <map>
#include <vector>

#define RETURN_SUCCESS 0
#define RETURN_BAD_PREMISE 1
#define RETURN_FEW_ARGS 2

#define LOGIC_FUNC(N) bool N(bool a, bool b)
#define LOGIC_FUNC_PTR(N) LOGIC_FUNC((*N))
#define ARG_DO(N) inline void N(int argc, char** args, int& i)

#define ATOMIC_RANK 99
using namespace std;

void usage(){
	cout << "logos [OPTIONS] [PREMISES]\n"
		"\t-h\tPrint this message\n"
		"\t-p\tPrint premises with logical symbols instead of '&|=' etc.\n"
		"\t-l\tRepresent given premises as atomic in table\n"
		"\t-d \"$\"\tSet delimiter of table\n";
	exit(0);
}

struct node{
    bool (*operation)(bool, bool);
    int atom;
    node* parent, *left, *right;
};

struct opr_info{
    LOGIC_FUNC_PTR(func);
    string pretty;
};

LOGIC_FUNC(EMPTY){ return 0; }
LOGIC_FUNC(ATOM){ return a; }
LOGIC_FUNC(NOT){ return !a; }
LOGIC_FUNC(AND){ return a && b; }
LOGIC_FUNC(OR){ return a || b; }
LOGIC_FUNC(IMPLICATION){ return !a || b; }
LOGIC_FUNC(EQUIVALENCE){ return (a && b) || (!a && !b); }

map<LOGIC_FUNC_PTR(), int> opRank = {
    {NOT, ATOMIC_RANK},
    {AND, 1},
    {OR, 2},
    {IMPLICATION, 3},
    {EQUIVALENCE, 4}
};

/*** PRETTY OPERATORS ***/
const string CH_NOT = " ¬";
const string CH_AND = " ⋂ ";
const string CH_OR = " ⋃ ";
const string CH_IMPLICATION = " → ";
const string CH_EQUIVALENCE = " ⟷ ";

map<string, opr_info> prettyOperators = {
    {"!", {NOT, CH_NOT}},
    {"~", {NOT, CH_NOT}},
    {"NOT", {NOT, CH_NOT}},
    {"&", {AND, CH_AND}},
    {"AND", {AND, CH_AND}},
    {"|", {OR, CH_OR}},
    {"OR", {OR, CH_OR}},
    {"->", {IMPLICATION, CH_IMPLICATION}},
    {"IMPLIES", {IMPLICATION, CH_IMPLICATION}},
    {"<->", {EQUIVALENCE, CH_EQUIVALENCE}},
    {"=", {EQUIVALENCE, CH_EQUIVALENCE}},
    {"EQUALS", {EQUIVALENCE, CH_EQUIVALENCE}}
};

map<LOGIC_FUNC_PTR(), string> unprettyOperators = {
	{EMPTY, "X"},
	{NOT, "!"},
	{AND, "&"},
	{OR, "|"},
	{IMPLICATION, "->"},
	{EQUIVALENCE, "<->"}
};

/******************/

node __EMPTY_NODE = {EMPTY, -1};
node* EMPTY_NODE = &__EMPTY_NODE;

size_t ATOM_COUNT;
map<char, int> ATOMS;
vector<char> ATOM_BY_IND;

/*** FUNCTIONS ***/
bool evaluate(node* n, bool* atoms){
    if(n->atom > -1){
        return n->operation(atoms[n->atom], 0);
    }else if(opRank[n->operation] == ATOMIC_RANK){
        return n->operation(evaluate(n->left, atoms), 0);
    }else{
        return n->operation(evaluate(n->left, atoms), evaluate(n->right, atoms));
    }
}

void reterrn(string msg, int r, string premise, int place = -1){
    cerr << msg << "\n";
    if(place > -1){
        cerr << '\t'
             << string(place, ' ') << "*\n\t"
             << premise << "\n\t"
             << string(place, ' ') << "*\n";
    }
    exit(r);
}

inline size_t outcomeCount(){
    return 2 << (ATOM_COUNT - 1);
}

inline void printAtoms(uint64_t input, string delim){
    for(uint64_t j = 1 << (ATOM_COUNT - 1); j; j >>= 1){
        cout << (bool) (input & j) << delim;
    }
}

inline uint64_t bitMaskOf(char atom){
    return 1 << ATOMS[atom];
}

inline bool atomState(uint64_t atomTable, char atom){
	return atomTable & bitMaskOf(atom);
}

/**
 *  must be used after all premises have been parsed into trees
 */
void generateTable(node* premise, bool* table){
	/**
	 * inp is a bitmap of all atomic premises where
	 * when a is true
	 * 		b is true
	 * 		c is false
	 * 		d is true
	 * 	inp is
	 * 		1101
	 *		^^ ^
	 *		abcd
	 *
	 *	it is also the index of the truth table
	 */
    uint64_t inp = outcomeCount();
    
	//to store values of atoms to pass to evaluate function
    bool atoms[ATOM_COUNT];
    do{
		//test each atom
        uint64_t head = 1 << (ATOM_COUNT - 1);
        for(int i = 0; i < ATOM_COUNT; i++){
            atoms[i] = inp & head;
            head >>= 1;
        }
        
		//save truth state of premise
        table[inp] = evaluate(premise, atoms);
    }while(inp--);
}

bool matchOpr(LOGIC_FUNC_PTR(*trg), string& premise, int* i){
    int kool = i ? *i : 0;
    string opr;
    do{
        opr.append(1, premise[kool++]);
    }while(!prettyOperators.count(opr) && !(premise[kool] >= 'a' && premise[kool] <= 'z'));

    if(!prettyOperators.count(opr)) return false;
    
    if(i) *i = kool - 1;
    if(trg) *trg = prettyOperators[opr].func;
    return true;
}

void printNodeTree(node* n, int t = 0, bool r = true){
	if(!n || n->operation == EMPTY) return;

	cout << string(r ? 0 : t, '\t') << unprettyOperators[n->operation] << "[" << n->atom << "]\t";

	printNodeTree(n->right, t+1);
	cout << '\n';
	printNodeTree(n->left, t, false);
}

void clearNode(node* n){
	n->atom = -1;
	n->left = nullptr;
	n->right = nullptr;
	n->operation = nullptr;
	n->parent = nullptr;
}

/********************* PARSE ************************************************************************************************************/
node* parse(string premise){
    node* point = nullptr;
    vector<node*> atomStack;
//    int atomCount = ATOMS.size();
    
    vector<node*> oprStack;
    
    node* atomOpr = nullptr;
    
    int pp = -1;
    
    //translate text to operation tree
    for(int i = 0; i < premise.size(); i++){
        char& c = premise[i];
        if(c == ' ') continue;
        
        if(c >= 'a' && c <= 'z'){
            if(pp == 0) reterrn("Ungrammatical! Multiple premises with no connective!", RETURN_BAD_PREMISE, premise, i);
            pp = 0;
            
//			cout << "encountered atom " << c << "\n";
            if(!ATOMS.count(c)){
//				cout << "SET to " << ATOM_COUNT << '\n';
                ATOMS[c] = ATOM_COUNT++;
                ATOM_BY_IND.push_back(c);
//				cout << ATOM_BY_IND.size() << '\n';
            }
            
            node* subnode = new node;
			clearNode(subnode);
            subnode->operation = ATOM;
            subnode->atom = ATOMS[c];
            
            if(atomOpr){
                atomOpr->left = subnode;
                subnode = atomOpr;
                while(subnode->parent) subnode = subnode->parent;
                atomOpr = nullptr;
            }
            
            atomStack.push_back(subnode);
        }else if(c == '('){
            if(pp == 0) reterrn("Ungrammatical! Multiple premises with no connective!", RETURN_BAD_PREMISE, premise, i);
			pp = 0;

            int pst = 1, j = i + 1;
            while(pst && j < premise.size()){
                if(premise[j] == ')') pst--;
                else if(premise[j] == '(') pst++;
                j++;
            }

            node* subnode = parse(premise.substr(i + 1, j - i - 2));

			if(atomOpr){
                atomOpr->left = subnode;
                subnode = atomOpr;
                while(subnode->parent) subnode = subnode->parent;
                atomOpr = nullptr;
            }

            atomStack.push_back(subnode);

            i = j - 1;
        }else{
            node* subnode = new node;
			clearNode(subnode);
            
            //match operator string to logic func pointer and set subnode operation to that
            if(!matchOpr(&subnode->operation, premise, &i)) reterrn("Invalid operator!", RETURN_BAD_PREMISE, premise, i);
            
            //if atomic rank, therefor single argument
            if(opRank[subnode->operation] == ATOMIC_RANK){
                pp = 2;
                subnode->right = EMPTY_NODE;
                
                if(!atomOpr){
                    atomOpr = subnode;
                }else{
                    atomOpr->left = subnode;
                    subnode->parent = atomOpr;
                    atomOpr = atomOpr->left;
                }
                
                continue;
            }
            
            if(pp == 1) reterrn("Ungrammatical! Connectives with no premise!", RETURN_BAD_PREMISE, premise, i);
            pp = 1;
            
            oprStack.push_back(subnode);
            
            if(point){
                bool lesser = opRank[subnode->operation] < opRank[point->operation];
                
                if(lesser){
                    subnode->parent = point;
                    
                    if(!point->right){
                        point->right = subnode;
                    }else{
                        point->left = subnode;
                    }
                }else{
                    //traverse up until hit operation with greater or equal rank
                    while(point->parent && (opRank[subnode->operation]) <= opRank[point->parent->operation]){
                        point = point->parent;
                    }

                    if(!point->parent){
                        subnode->left = point;
                        point->parent = subnode;
                    }else{
                        point->left->parent = subnode;
                        subnode->parent = point;
                    }
                }
            }
            
            if(atomOpr){
                if(subnode->parent){
                    node** place;
                    if(subnode == subnode->parent->left){
                        place = &subnode->parent->left;
                    }else if(subnode == subnode->parent->left){
                        place = &subnode->parent->right;
                    }
                    
                    node* topAtomOpr = atomOpr;
                    while(topAtomOpr->parent) topAtomOpr = topAtomOpr->parent;
                    *place = topAtomOpr;
                }
                
                subnode->parent = atomOpr;
                atomOpr->left = subnode;
                
                atomOpr = nullptr;
            }
            
            point = subnode;
        }
    }
    
	if(pp) reterrn("Ungrammatical! Missing premise!", RETURN_BAD_PREMISE, premise, premise.size());

    //populate operations with atoms
    if(!point){
        point = *atomStack.rbegin();
        atomStack.pop_back();
    }else{
        while(oprStack.size()){
            point = *oprStack.rbegin();

            if(!point->right){
                point->right = *atomStack.rbegin();
                atomStack.pop_back();
            }
            
            if(!point->left){
                point->left = *atomStack.rbegin();
                atomStack.pop_back();
            }
            
            oprStack.pop_back();
        }
    }
    
    //traverse up to master node
    while(point->parent) point = point->parent;

//	cout << "PARSED: " << premise << '\n';
//	printNodeTree(point);
//	cout << "\n\n";

    return point;
}

/*** ARGUMENTS ***/

void argCountCheck(int argc, char** args, int i){
	if(i >= argc - 1) reterrn("Too few arguments! Missing argument for " + string(args[i]), RETURN_FEW_ARGS, "");
}

struct{
    bool pretty = 0;
    bool list = 0;
    string delim = " | ";
	vector<string> assertPremises;
	vector<bool*> assertTables;
}ARGUMENTS;

ARG_DO(_arg_help) {
	usage();
}

ARG_DO(_arg_pretty) { ARGUMENTS.pretty = 1; }
ARG_DO(_arg_list)   { ARGUMENTS.list = 1; }

ARG_DO(_arg_delim)  {
	argCountCheck(argc, args, i);
    ARGUMENTS.delim = string(args[++i]);
}

ARG_DO(_arg_assert) {
	argCountCheck(argc, args, i);
	ARGUMENTS.assertPremises.push_back(string(args[++i]));
}

/*** MAIN ***/
//TODO maybe make the formatting a bit nicer
//TODO add arguments -M[macro] 
//TODO --assert-not[premise]
int main(int argc, char** args){
    if(argc < 2) reterrn("Too few arguments!", RETURN_FEW_ARGS, "");
    
    //handle arguments
    map<string, void(*)(int, char**, int&)> argStrs = {
		{"-h", _arg_help},
		{"--help", _arg_help},
        {"-p", _arg_pretty},
        {"--pretty", _arg_pretty},
        {"-l", _arg_list},
        {"-d", _arg_delim},
		{"-A", _arg_assert},
		{"--assert", _arg_assert},
    };

    vector<string> premises;
    for(int i = 1; i < argc; i++){
        string arg(args[i]);
        if(!arg.size()) continue;

        if(arg[0] == '-'){
            if(argStrs.count(arg)) argStrs[arg](argc, args, i);
        }else{
            premises.push_back(arg);
        }
    }
    
    if(!premises.size()) reterrn("Too few arguments! Must give at least one premise!", RETURN_FEW_ARGS, "");
    
    //parse premises
    vector<node*> parsed;
	for(string premise : premises){
		parsed.push_back(parse(premise));
	}

	vector<node*> asserts;
	for(string premise : ARGUMENTS.assertPremises){
		asserts.push_back(parse(premise));
	}

	//generate tables
    vector<bool*> tables;
	for(node* n : parsed){
        bool* ntable = new bool[outcomeCount()];
        tables.push_back(ntable);
        
        generateTable(n, ntable);
    }

	for(node* n : asserts){
        bool* ntable = new bool[outcomeCount()];
        ARGUMENTS.assertTables.push_back(ntable);
        
        generateTable(n, ntable);
    }
    
    //print table
    if(ARGUMENTS.pretty){
        for(string& str : premises){
            //remove spaces;
            for(auto it = str.begin(); it < str.end();){
                if(*it == ' '){
                    str.erase(it);
                }else{
                    it++;
                }
            }

            //replace operator strings with special chars
            for(int i = 0; i < str.size(); i++){
                int j = i;
                if(matchOpr(nullptr, str, &j)){
                    str.replace(i, j + 1 - i, prettyOperators[str.substr(i, j + 1 - i)].pretty);
                }
            }
        }
    }
    
    if(ARGUMENTS.list){
        char c = 'p';
        
        for(string& str : premises){
            cout << c << " = " << str << '\n';
            str = string(1, c);
            c++;
        }
    }
    
    string& d = ARGUMENTS.delim;
    
    cout << ATOM_BY_IND[0];
    for(int i = 1; i < ATOM_COUNT; i++){
        cout << d << ATOM_BY_IND[i];
    }
    cout << d;
    
    cout << premises[0];
    for(int i = 1; i < premises.size(); i++){
        cout << d << premises[i];
    }
    cout << '\n';
    
    uint64_t inp = outcomeCount() - 1;
    do{
		bool r = false;
		for(bool* assTable : ARGUMENTS.assertTables){
//			cout << assTable[inp] << '\n';
			if(!assTable[inp]){
				r = true;
				break;
			}
		}
		if(r) continue;

        printAtoms(inp, d);
        
        cout << tables[0][inp];
        for(int j = 1; j < tables.size(); j++){
            cout << d << tables[j][inp];
        }
        cout << "\n";
    }while(inp--);
    
    return RETURN_SUCCESS;
}
