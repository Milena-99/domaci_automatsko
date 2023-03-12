#include <iostream>
#include <memory>
#include <map>

struct Formula;
using FormulaPtr = std::shared_ptr<Formula>;
using Valuation = std::map<unsigned, bool>;

struct FalseData  { };
struct TrueData   { };
struct AtomData   { unsigned n; };
struct NotData    { FormulaPtr f; };
struct BinaryData {
    enum Type {
        And,
        Or
    } type;

    FormulaPtr l;
    FormulaPtr r;
};

struct Formula {
    enum Type {
        False,
        True,
        Atom,
        Not,
        Binary
    } type;

    union {
        AtomData atomData;
        NotData notData;
        BinaryData binaryData;
    };

    Formula(FalseData)    : type(False)                 { }
    Formula(TrueData)     : type(True)                  { }
    Formula(AtomData d)   : type(Atom), atomData(d)     { }
    Formula(NotData d)    : type(Not), notData(d)       { }
    Formula(BinaryData d) : type(Binary), binaryData(d) { }
    ~Formula() {
        switch(type) {
        case Not: notData.~NotData(); break;
        case Binary: binaryData.~BinaryData(); break;
        default: {}
        }
    }
};

FormulaPtr False() { return std::make_shared<Formula>(FalseData{}); }
FormulaPtr True()  { return std::make_shared<Formula>(TrueData{}); }
FormulaPtr Atom(unsigned n) { return std::make_shared<Formula>(AtomData{n}); }
FormulaPtr Not(FormulaPtr f) { return std::make_shared<Formula>(NotData{f}); }
FormulaPtr Binary(BinaryData::Type t, FormulaPtr l, FormulaPtr r) {
    return std::make_shared<Formula>(BinaryData{t, l, r});
}
FormulaPtr And(FormulaPtr l, FormulaPtr r)  { return Binary(BinaryData::Type::And,  l, r); }
FormulaPtr Or(FormulaPtr l, FormulaPtr r)   { return Binary(BinaryData::Type::Or,   l, r); }

void printFormula(FormulaPtr formula) {
    switch(formula->type) {
    case Formula::Type::False: std::cout << "F"; break;
    case Formula::Type::True:  std::cout << "T"; break;

    case Formula::Type::Atom:
        std::cout << "p" << formula->atomData.n;
        break;

    case Formula::Type::Not:
        std::cout << "~";
        printFormula(formula->notData.f);
        break;

    case Formula::Type::Binary:
        std::cout << "(";
        printFormula(formula->binaryData.l);

        switch(formula->binaryData.type) {
        case BinaryData::Type::And:  std::cout << " & "; break;
        case BinaryData::Type::Or:   std::cout << " | "; break;
        }

        printFormula(formula->binaryData.r);
        std::cout << ")";
        break;
    }
}

unsigned max(unsigned m1, unsigned m2){
    return m1 > m2 ? m1 : m2;
}

unsigned max_depth(FormulaPtr formula, unsigned &m) {
    switch(formula->type) {
    case Formula::Type::False:
    case Formula::Type::True:
    case Formula::Type::Atom:
        return m;
    case Formula::Type::Not:
        m=max(m, 1 + max_depth(formula->notData.f, m));
        return m;
    case Formula::Type::Binary:
        m=max(m, 1 + max(max_depth(formula->binaryData.l, m),
                     max_depth(formula->binaryData.r, m)));
        return m;
    }
}


int main()
{
    FormulaPtr p0 = Atom(0);
    FormulaPtr p1 = Atom(1);
    FormulaPtr p2 = Atom(2);
    FormulaPtr notp1 = Not(p1);
    FormulaPtr or1 = Or(notp1, p2);
    FormulaPtr leftF = And(p0, or1);
    FormulaPtr F = Or(leftF, p1);
    printFormula(F); std::cout << std::endl;
    unsigned m=0;
    std::cout << max_depth(F, m) << std::endl;

    FormulaPtr moja1=And(p2,notp1);

    FormulaPtr moja2=And(p0, p1);
    FormulaPtr moja3=Or(moja1, moja2);
    printFormula(And(p1, moja3)); std::cout << std::endl;
    m=0;
    std::cout << max_depth(moja3, m) << std::endl;

    return 0;
}










