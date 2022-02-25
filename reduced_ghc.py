#============================================#
# UE Calculabilite L3                        #
# TME GHC reduites                           #
# Mathieu.Jaume@lip6.fr                      #
#============================================#

from ghc import *

# Symboles productifs
# -------------------

def prod0(t,r):
    # t : symboles terminaux
    # r : liste de productions
    p0 = []
    for s,ls in r: # Parcours des liste de productions s -> list(prod)
        for p in ls: # Parcours des produductions prod
            for p_symb in p: # Parcours des symboles de la production
                if p_symb not in t:
                    break
            else:
                p0.append(s)
    return p0

def next_prod(t,r,eqnt,prev):
    # t : symboles terminaux
    # r : liste de productions
    # eqnt : egalite sur les non terminaux
    # prev : liste de non terminaux de depart
    nextp = prev
    for s,ls in r: # Parcours des liste de productions s -> list(prod)
        for p in ls: # Parcours des produductions prod
            for p_symb in p: # Parcours des symboles de la production
                if p_symb not in t and not is_in(eqnt,p_symb,prev):
                    break
            else:
                nextp = ajout(eqnt,s,nextp)
    return nextp


def prod(t,r,eqnt):
    # t : symboles terminaux
    # r : liste de productions
    # eqnt : egalite sur les non terminaux
    # A COMPLETER
    return fixpoint_from(make_eq_set(eqnt),lambda prev : next_prod(t,r,eqnt,prev),prod0(t,r))

# Elimination des symboles non productifs d'une GHC
# -------------------------------------------------

# elimination de non-terminaux n'appartenant pas a l'ensemble ent (ainsi que
# des productions contenant un symbole n'appartenant pas a ent

def remove_nt(g,ent):
    # g : ghc
    # ent : symboles non terminaux
    nt,t,r,si,eqnt = g
    def is_terminal(x):
        return is_in(eq_atom,x,t)
    def is_in_ent(x):
        return is_in(eqnt,x,ent)
    def is_in_ent_or_terminal(x):
        return is_in_ent(x) or is_terminal(x)
    def all_in_ent_or_terminal(l):
        return forall_such_that(l,is_in_ent_or_terminal)
    new_r = [(s,[l for l in ls if all_in_ent_or_terminal(l)]) \
             for s,ls in r if is_in_ent(s)]
    if is_in_ent(si):
        return (ent,t,new_r,si,eqnt)
    else:
        return (ent,t,new_r,None,eqnt)


def remove_non_prod(g):
    # g : ghc
    # A COMPLETER
    (_,t,r,_,eqnt) = g
    return remove_nt(g,prod(t,r,eqnt))

# Symboles accessibles
# --------------------

def next_reach(nt,r,eqnt,prev):
    # nt : symboles non terminaux
    # r : liste de productions
    # eqnt : egalite sur les non terminaux
    # prev : liste de non terminaux de depart
    nextr = prev
    for y in prev:
        for u in prods_s(r,eqnt,y):
            for x in u:
                if is_in(eqnt,x,nt):
                    nextr = ajout(eqnt,x,nextr)
    return nextr

def reach(nt,r,si,eqnt):
    # nt : symboles non terminaux
    # r : liste de productions
    # si : symbole de depart
    # eqnt : egalite sur les non terminaux
    # A COMPLETER
    return fixpoint_from(make_eq_set(eqnt),lambda prev : next_reach(nt,r,eqnt,prev),[si])

# Elimination des symboles non accessibles d'une GHC
# -------------------------------------------------

def remove_non_reach(g):
    # g : ghc
    # A COMPLETER
    (nt,_,r,si,eqnt) = g
    return remove_nt(g,reach(nt,r,si,eqnt))

# Reduction d'une grammaire hors-contexte
# ---------------------------------------

def reduce_grammar(g):
    # g : ghc
    # A COMPLETER
    return remove_non_reach(remove_non_prod(g))
