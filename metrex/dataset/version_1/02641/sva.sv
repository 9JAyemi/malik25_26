// SVA checkers for the provided DUTs.
// Bind these modules in your testbench or a top-level wrapper.

//////////////////// Concat ////////////////////
module Concat_sva;
  default clocking cb @(posedge clock); endclocking

  // Requests: exactly one side selected when req=1; none when req=0
  assert property (req |-> (listA_req ^ listB_req));
  assert property (!req |-> (listA_req==0 && listB_req==0));

  // Data/ack routing matches selection
  assert property (selectA |-> (listA_req==req && listB_req==0 &&
                                ack==listA_ack && value==listA_value &&
                                value_valid==listA_value_valid));
  assert property (!selectA |-> (listB_req==req && listA_req==0 &&
                                 ack==listB_ack && value==listB_value &&
                                 value_valid==listB_value_valid));

  // lastSelectA update protocol
  assert property (ready |=> lastSelectA == $past(selectA));
  assert property (!ready |=> lastSelectA == 1'b1);

  // Coverage: both paths and A->B switch when A ack with invalid
  cover property (selectA);
  cover property (!selectA);
  cover property (ready && selectA && listA_ack && !listA_value_valid ##1 !selectA);
endmodule
bind Concat Concat_sva ccat_chk();


//////////////////// Cons ////////////////////
module Cons_sva;
  default clocking cb @(posedge clock); endclocking

  // Reset behavior on not-ready
  assert property (!ready |=> headShown==0 && selectHead==1 && headAck==0);

  // Rising req under ready causes headAck pulse and marks head shown
  assert property (ready && !$past(req) && req |=> headAck==1 && headShown==1);
  assert property (headAck |=> !headAck);

  // If head already shown when req rises, tail is selected next cycle
  assert property (ready && !$past(req) && req && $past(headShown) |=> selectHead==0);

  // Output routing per selection
  assert property (selectHead |-> (ack==headAck && value==head &&
                                   value_valid==1 && tail_req==0));
  assert property (!selectHead |-> (tail_req==req && ack==tail_ack &&
                                    value==tail_value && value_valid==tail_value_valid));

  // Coverage: head first then tail on a request
  cover property (ready && $rose(req) ##1 !selectHead);
endmodule
bind Cons Cons_sva cons_chk();


//////////////////// Hold ////////////////////
module Hold_sva;
  default clocking cb @(posedge clock); endclocking

  // Functional next-state
  assert property (ready |=> y == ($past(y) | $past(x)));
  assert property (!ready |=> y == 1'b0);

  // Monotonic while ready
  assert property (ready && $past(y) |-> y);
endmodule
bind Hold Hold_sva hold_chk();


//////////////////// ListMux ////////////////////
module ListMux_sva;
  // Combinational immediate assertions
  always @* begin
    if (!ready) begin
      assert (true_req==0 && false_req==0 &&
              out_ack==0 && out_value==8'hFF && out_value_valid==0);
    end else if (cond) begin
      assert (true_req==out_req && false_req==0 &&
              out_ack==true_ack && out_value==true_value &&
              out_value_valid==true_value_valid);
    end else begin
      assert (false_req==out_req && true_req==0 &&
              out_ack==false_ack && out_value==false_value &&
              out_value_valid==false_value_valid);
    end
    assert (!(true_req && false_req)); // mutual exclusion
    cover (ready && cond && out_req);
    cover (ready && !cond && out_req);
  end
endmodule
bind ListMux ListMux_sva lmux_chk();


//////////////////// Decons ////////////////////
module Decons_sva;
  default clocking cb @(posedge clock); endclocking

  // Reset behavior on not-ready
  assert property (!ready |=> done==0 && nextDone==0 && head==8'hFF && head_valid==0);

  // Capture and done protocol
  assert property (ready && !done && list_ack |-> nextDone);          // capture cycle
  assert property (ready && !done && list_ack |=> done==1);           // done sets next cycle
  assert property (nextDone |-> $past(ready) && !$past(done) && $past(list_ack));
  assert property (ready && $past(done) |-> done);                    // done sticky while ready

  // Head/value capture (checked one cycle later for stability)
  assert property (ready && !done && list_ack |=> head==$past(list_value) &&
                                            head_valid==$past(list_value_valid));

  // Routing based on done
  assert property (done |-> (list_req==tail_req &&
                             tail_ack==list_ack &&
                             tail_value==list_value &&
                             tail_value_valid==list_value_valid));
  assert property (!done |-> (list_req==(ready && !nextDone) &&
                              tail_ack==0 && tail_value==8'hFF &&
                              tail_value_valid==0));

  // Coverage: capture, forward, and reset
  cover property (ready && !done && list_ack);
  cover property (done && tail_req);
  cover property (!ready ##1 !done);
endmodule
bind Decons Decons_sva dcons_chk();