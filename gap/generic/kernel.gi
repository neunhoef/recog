#############################################################################
##
##  This file is part of recog, a package for the GAP computer algebra system
##  which provides a collection of methods for the constructive recognition
##  of groups.
##
##  This files's authors include Sergio Siccha.
##
##  Copyright of recog belongs to its developers whose names are too numerous
##  to list here. Please refer to the COPYRIGHT file for details.
##
##  SPDX-License-Identifier: GPL-3.0-or-later
##
##
##  Implementation of recog methods
##
#############################################################################

# Helper function for FindKernelRandom and RecogniseGeneric.
# Generate `n` random kernel elements for `ri` and return a boolean. If
# `onlyGenerate` is true, then add the kernel elements directly to `gensN(ri)`.
# Otherwise, ask the kernel node to write the random kernel elements as SLPs in
# the kernel node's nice generators.
# The return value is `fail`, iff computing an SLP for a random element of the
# group behind the image node of `ri` failed. This indicates, that something
# went wrong during recognition of the image.
# If the return value is not `fail`, then it is `false` if for any random kernel
# element it was not possible to write it as an SLP in the kernel node's nice
# generators. Otherwise it is `true`. Hence, the return value can only be
# `false`, if `onlyGenerate` is `false`.
BindGlobal( "GenerateRandomKernelElementsAndOptionallyVerifyThem",
  function(ri, n, onlyGenerate)
    local gens, verificationSuccess, x, s, y, z, i;
    gens := gensN(ri);
    verificationSuccess := true;
    # We generate a random element of the kernel as the quotient of a random
    # element and the preimage of its image under the homomorphism.
    for i in [1 .. n] do
        # Finding kernel generators and immediate verification must use
        # different random elements! This is ensured by using the same stamp
        # in both situations.
        x := RandomElm(ri, "GenerateRandomKernelElementsAndOptionallyVerifyThem", true).el;
        Assert(2, ValidateHomomInput(ri, x));
        s := SLPforElement(ImageRecogNode(ri),
                                 ImageElm(Homom(ri), x!.el));
        if s = fail then
            return fail;
        fi;
        y := ResultOfStraightLineProgram(s, ri!.pregensfacwithmem);
        z := x^-1*y;
        if isone(ri)(z) or ForAny(gens, x -> isequal(ri)(x, z)) then
            continue;
        fi;
        if onlyGenerate or SLPforElement(KernelRecogNode(ri), z!.el) = fail then
            Add(gens, z);
            verificationSuccess := false;
        fi;
    od;
    return verificationSuccess;
  end );

InstallGlobalFunction( ImmediateVerification,
  function(ri)
    local verified;
    verified := GenerateRandomKernelElementsAndOptionallyVerifyThem(
        ri,
        RECOG_NrElementsInImmediateVerification,
        false
    );
    if verified = fail then
        ErrorNoReturn("Very bad: image was wrongly recognised ",
                      "and  we found out too late");
    fi;
    if verified = true then return true; fi;
    # Now, verified = false.
    Info(InfoRecog,2,
         "Immediate verification: found extra kernel element(s)!");
    if FindKernelFastNormalClosure(ri,5,5) = fail then
        ErrorNoReturn("Very bad: image was wrongly recognised ",
                      "and  we found out too late");
    fi;
    Info(InfoRecog,2,"Have now ",Length(gensN(ri)),
         " generators for kernel.");
    return false;
  end );

InstallGlobalFunction( FindKernelRandom,
  function(ri,n)
    local res;
    Info(InfoRecog,2,"Creating ",n," random generators for kernel.");
    # We need to be careful with creating trivial kernels because we may want
    # to do immediate verification. If we find only trivial generators for the
    # kernel, then the kernel node of `ri` is set to `fail`. However, then
    # doing immediate verification would become a bit complicated. On the other
    # hand, creating a kernel node with only a trivial generator breaks all
    # kinds of other functions. So instead, when we find only trivial
    # generators we generate more random kernel elements. This is equivalent
    # to doing one immediate verification.
    res := GenerateRandomKernelElementsAndOptionallyVerifyThem(ri, n, true);
    if res = fail then return fail; fi;
    if IsEmpty(gensN(ri)) and immediateverification(ri) then
        Info(InfoRecog,2,"Found only trivial generators for the kernel. ",
             "Doing immediate verification.");
        res := GenerateRandomKernelElementsAndOptionallyVerifyThem(
            ri,
            RECOG_NrElementsInImmediateVerification,
            true
        );
    fi;
    return res;
  end );

InstallGlobalFunction( FindKernelDoNothing,
  function(ri,n1,n2)
    return true;
  end );

# Returns the product of a subsequence of a list (of generators).
# An entry in the original list is chosen for the subsequence with
# probability 1/2.
InstallGlobalFunction( RandomSubproduct, function(a)
    local prod, list, g;

    if IsGroup(a) then
        prod := One(a);
        list := GeneratorsOfGroup(a);
    elif IsList(a) then
        if Length(a) = 0 or
            not IsMultiplicativeElementWithInverse(a[1]) then
            ErrorNoReturn("<a> must be a nonempty list of group elements");
        fi;
        prod := One(a[1]);
        list := a;
    else
        ErrorNoReturn("<a> must be a group or a nonempty list of group elements");
    fi;

    for g in list do
        if Random( [ true, false ] )  then
            prod := prod * g;
        fi;
    od;
    return prod;
end );

# Computes randomly (it might underestimate) the normal closure of <list>
# under conjugation by the group generated by <grpgens>.
InstallGlobalFunction( FastNormalClosure , function( grpgens, list, n )
  local i,list2,randgens,randlist;
  if IsEmpty(list) then
    Print("empty gens list\n");
    return [];
  fi;
  list2 := ShallowCopy(list);
  fewGenerators := Length(grpgens) <= 3
  if fewGenerators then
    repetitions := 3 * n;
  else
    repetitions := 6 * n
  fi;
  for i in [1..repetitions] do
    if Length(list2)=1 then
      randlist := list2[1];
    else
      randlist := RandomSubproduct(list2);
    fi;
    if IsOne(randlist) then
      continue;
    fi;
    # for short generator lists, conjugate with all generators
    if fewGenerators then
      conjugators := grpgens;
    else
      conjugators := [RandomSubproduct(grpgens)];
    fi;
    for c in conjugators do
      if not IsOne(c) then
        new := randlist ^ c;
        if not new in list2 then
          Add(list2,randlist ^ c);
        fi;
      fi;
    od;
    fi;
  od;
  return list2;
end );

# FIXME: rename FindKernelFastNormalClosure to indicate that it *also* computes random generators
InstallGlobalFunction( FindKernelFastNormalClosure,
  # Used in the generic recursive routine.
  function(ri,n1,n2)
    if FindKernelRandom(ri, n1) = fail then
        return fail;
    fi;

    SetgensN(ri,FastNormalClosure(ri!.gensHmem,gensN(ri),n2));

    return true;
  end);
