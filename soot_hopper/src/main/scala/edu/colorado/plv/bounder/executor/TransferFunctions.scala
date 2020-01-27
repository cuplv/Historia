package edu.colorado.plv.bounder.executor

import edu.colorado.plv.bounder.ir.{CmdWrapper, Invoke, InvokeCmd, Loc, SpecialInvoke, StaticInvoke, VirtualInvoke}
import edu.colorado.plv.bounder.state.{BottomQry, Qry, SomeQry, Val}
import soot.jimple.internal.JInvokeStmt

class TransferFunctions[C,M] {
  def targetSelector(inv: JInvokeStmt):Set[Loc] = ???

  def transfer(post:Qry, cmd: CmdWrapper[C,M]) : Set[Qry] = post match{
    case SomeQry(stack, loc) => cmd match{
      case InvokeCmd(method, loc, w) => ???
      case a =>
        ???
    }
    case BottomQry(loc) => Set()
  }

  /**
   *
   * @param post
   * @param cmd
   * @param result - abstract value of return from method
   * @return
   */
  def transferInvoke(post:Qry, cmd:Invoke, result: Val) : Set[Qry] = cmd match {
    case VirtualInvoke(target, targetClass, targetMethod, params) => ???
    case SpecialInvoke(target, targetClass, targetMethod, params) => ???
    case StaticInvoke(targetClass, targetMethod, params) => ???
  }

}
