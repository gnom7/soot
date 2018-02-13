/* Soot - a J*va Optimization Framework
 * Copyright (C) 1997-1999 Raja Vallee-Rai
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the
 * Free Software Foundation, Inc., 59 Temple Place - Suite 330,
 * Boston, MA 02111-1307, USA.
 */

package soot.jbco.bafTransformations;

import soot.Body;
import soot.BodyTransformer;
import soot.ByteType;
import soot.IntType;
import soot.IntegerType;
import soot.Local;
import soot.PatchingChain;
import soot.RefType;
import soot.SootField;
import soot.SootMethod;
import soot.Trap;
import soot.Type;
import soot.Unit;
import soot.baf.Baf;
import soot.baf.GotoInst;
import soot.baf.IdentityInst;
import soot.baf.JSRInst;
import soot.baf.TargetArgInst;
import soot.baf.ThrowInst;
import soot.jbco.IJbcoTransform;
import soot.jbco.jimpleTransformations.FieldRenamer;
import soot.jbco.util.BodyBuilder;
import soot.jbco.util.Rand;
import soot.jbco.util.ThrowSet;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Stack;

import static java.util.stream.Collectors.toList;

/**
 * @author Michael Batchelder
 * <p>
 * Created on 2-May-2006
 * <p>
 * This transformer takes a portion of gotos/ifs and moves them into a TRY/CATCH block
 */
public class IndirectIfJumpsToCaughtGotos extends BodyTransformer implements IJbcoTransform {

    public static String dependancies[] = new String[]{"bb.jbco_iii", "bb.jbco_ful", "bb.lp"};
    public static String name = "bb.jbco_iii";

    public String[] getDependancies() {
        return dependancies;
    }

    public String getName() {
        return name;
    }

    public void outputSummary() {
        out.println("Indirected Ifs through Traps: " + count);
    }

    private int count = 0;

    protected void internalTransform(Body b, String phaseName, Map<String, String> options) {
        int weight = soot.jbco.Main.getWeight(phaseName, b.getMethod().getSignature());
        if (weight == 0) {
            return;
        }

        PatchingChain<Unit> units = b.getUnits();
        Unit nonTrap = findNonTrappedUnit(b);
        if (nonTrap == null) {
            nonTrap = Baf.v().newNopInst();
            Unit last = units.stream()
                    .limit(Integer.MAX_VALUE)
                    .filter(u -> u instanceof IdentityInst)
                    .filter(u -> ((IdentityInst) u).getLeftOp() instanceof Local)
                    .reduce((u1, u2) -> u2)
                    .orElse(null);

            if (last != null) {
                units.insertAfter(nonTrap, last);
            } else {
                units.addFirst(nonTrap);
            }
        }

        Stack<Type> stack = StackTypeHeightCalculator.getAfterStack(b, nonTrap);

        List<Unit> addedUnits = new ArrayList<>();
        Iterator<Unit> it = units.snapshotIterator();
        while (it.hasNext()) {
            Unit u = it.next();
            if (isIf(u) && Rand.getInt(10) <= weight) {
                TargetArgInst ifu = (TargetArgInst) u;
                Unit newTarg = Baf.v().newGotoInst(ifu.getTarget());
                units.add(newTarg);
                ifu.setTarget(newTarg);
                addedUnits.add(newTarg);
            }
        }

        if (addedUnits.isEmpty()) {
            return;
        }

        Unit nop = Baf.v().newNopInst();
        units.add(nop);

        List<Unit> toinsert = new ArrayList<>();
        SootField field = null;
        try {
            field = FieldRenamer.getRandomOpaques()[Rand.getInt(2)];
        } catch (NullPointerException ignored) {
        }

        if (field != null && Rand.getInt(3) > 0) {
            toinsert.add(Baf.v().newStaticGetInst(field.makeRef()));
            if (field.getType() instanceof IntegerType) {
                toinsert.add(Baf.v().newIfGeInst(units.getSuccOf(nonTrap)));
            } else {
                SootMethod boolInit = ((RefType) field.getType()).getSootClass().getMethod("boolean booleanValue()");
                toinsert.add(Baf.v().newVirtualInvokeInst(boolInit.makeRef()));
                toinsert.add(Baf.v().newIfGeInst(units.getSuccOf(nonTrap)));
            }
        } else {
            toinsert.add(Baf.v().newPushInst(soot.jimple.IntConstant.v(BodyBuilder.getIntegerNine())));
            toinsert.add(Baf.v().newPrimitiveCastInst(IntType.v(), ByteType.v()));
            toinsert.add(Baf.v().newPushInst(soot.jimple.IntConstant.v(Rand.getInt() % 2 == 0 ? 9 : 3)));
            toinsert.add(Baf.v().newRemInst(ByteType.v()));

      /*toinsert.add(Baf.v().newDup1Inst(ByteType.v()));
      toinsert.add(Baf.v().newPrimitiveCastInst(ByteType.v(),IntType.v()));
      toinsert.add(Baf.v().newStaticGetInst(sys.getFieldByName("out").makeRef()));
      toinsert.add(Baf.v().newSwapInst(IntType.v(),RefType.v()));
      ArrayList parms = new ArrayList();
      parms.add(IntType.v());
      toinsert.add(Baf.v().newVirtualInvokeInst(out.getMethod("println",parms).makeRef()));
      */
            toinsert.add(Baf.v().newIfEqInst(units.getSuccOf(nonTrap)));
        }

        List<Unit> toinserttry = new ArrayList<>();
        while (stack.size() > 0) {
            toinserttry.add(Baf.v().newPopInst(stack.pop()));
        }
        toinserttry.add(Baf.v().newPushInst(soot.jimple.NullConstant.v()));

        Unit handler = Baf.v().newThrowInst();
        int rand = Rand.getInt(toinserttry.size());
        while (rand++ < toinserttry.size()) {
            toinsert.add(toinserttry.get(0));
            toinserttry.remove(0);
        }
        if (toinserttry.size() > 0) {
            toinserttry.add(Baf.v().newGotoInst(handler));
            toinsert.add(Baf.v().newGotoInst(toinserttry.get(0)));
            units.insertBefore(toinserttry, nop);
        }

        toinsert.add(handler);
        units.insertAfter(toinsert, nonTrap);

        b.getTraps().add(Baf.v().newTrap(ThrowSet.getRandomThrowable(), addedUnits.get(0), nop, handler));

        count += addedUnits.size();
        if (addedUnits.size() > 0 && debug) {
            StackTypeHeightCalculator.calculateStackHeights(b);
            //StackTypeHeightCalculator.printStack(units, StackTypeHeightCalculator.calculateStackHeights(b), false);
        }
    }

    private Unit findNonTrappedUnit(Body body) {
        int intrap = 0;
        List<Unit> untrapped = new ArrayList<>();

        PatchingChain<Unit> units = body.getUnits();
        Iterator<Unit> it = units.snapshotIterator();
        while (it.hasNext()) {
            Unit u = it.next();
            for (Trap t : body.getTraps()) {
                if (u == t.getBeginUnit()) {
                    intrap++;
                } else if (u == t.getEndUnit()) {
                    intrap--;
                }
            }

            if (intrap == 0) {
                untrapped.add(u);
            }
        }

        List<Unit> untrappedFiltered = untrapped.stream()
                .filter(Unit::fallsThrough)
                .filter(u -> units.getSuccOf(u) != null)
                .filter(u -> !(units.getSuccOf(u) instanceof ThrowInst))
                .collect(toList());
        if (untrappedFiltered.isEmpty()) {
            return null;
        } else {
            return untrappedFiltered.get(Rand.getInt(untrappedFiltered.size()));
        }
    }

    private boolean isIf(Unit u) {
        // TODO: will a RET statement be a TargetArgInst?
        return (u instanceof TargetArgInst) && !(u instanceof GotoInst)
                && !(u instanceof JSRInst);
    }
}
