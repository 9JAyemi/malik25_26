// SVA for rbo_test
// Bind this module or include alongside the DUT. Focused, high-signal-coverage checks.

module rbo_test_sva;

  // Access DUT signals via bind (no ports).
  // default clock
  default clocking cb @(posedge clk); endclocking

  // 1) Synchronous reset values (checked when reset_gen is 1)
  assert property (@(posedge clk)
    reset_gen |->
      counter==0 && stage==0 && stage_iter==0 &&
      CAL==0 && SBI==0 && SPHI1==0 && SPHI2==0 &&
      SEB==1 && IS1==1 && IS2==0 && SR==1 &&
      RESET==1 && R12==1 && RBI==0 && RPHI1==1 && RPHI2==1 &&
      LE==0 && CS==0
  );

  // 2) Constants and never-changing outputs
  assert property (Vthr==16'h0025 && Aref==16'h0033 && Vana==16'h0066 && RG==16'h0033);

  default disable iff (reset_gen);

  // Outputs that must remain stable during run
  assert property ($stable({CAL,SBI,SPHI1,SPHI2,SEB,IS1,IS2,SR,RESET,R12,LE}));

  // 3) State/iterator/counter well-formedness
  assert property (stage inside {0,1});
  assert property ((stage==0) -> (stage_iter==0));
  assert property ((stage==1) -> (stage_iter inside {[0:128]}));
  assert property ((stage==0) -> (counter inside {[0:29]}));
  assert property ((stage==1) -> (counter inside {[0:3]}));

  // Counter progression
  assert property ((stage==0 && counter!=29) |=> counter==$past(counter)+1);
  assert property ((stage==0 && counter==29) |=> counter==0);
  assert property ((stage==1 && counter!=3)  |=> counter==$past(counter)+1);
  assert property ((stage==1 && counter==3)  |=> counter==0);

  // Stage transitions
  assert property ((stage==0 && counter==29) |=> (stage==1 && stage_iter==0 && counter==0));
  assert property ((stage==1 && counter==3 && stage_iter!=128) |=> (stage==1 && stage_iter==$past(stage_iter)+1 && counter==0));
  assert property ((stage==1 && counter==3 && stage_iter==128) |=> (stage==0 && stage_iter==0 && counter==0));

  // 4) Scheduled actions in stage 0
  assert property ((stage==0 && counter==7)  |-> RBI==1);
  assert property ((stage==0 && counter==16) |-> RBI==0);
  assert property ((stage==0 && counter==22) |-> (RPHI1==0 && RPHI2==0));
  assert property ((stage==0 && counter==24) |-> RBI==1);
  assert property ((stage==0 && counter==25) |-> RPHI1==1);
  assert property ((stage==0 && counter==26) |-> RPHI1==0);
  assert property ((stage==0 && counter==27) |-> RBI==0);
  assert property ((stage==0 && counter==28) |-> RPHI2==1);
  assert property ((stage==0 && counter==29) |-> RPHI2==0);

  // 5) Scheduled actions in stage 1
  assert property ((stage==1 && counter==1) |-> (RPHI1==0 && CS==1));
  assert property ((stage==1 && counter==2) |-> RPHI2==1);
  assert property ((stage==1 && counter==3) |-> RPHI2==0);

  // 6) Edge legality constraints
  // RBI only changes in stage 0 at specific counts; remains stable in stage 1
  assert property ((stage==0 && $rose(RBI)) |-> $past(counter) inside {7,24});
  assert property ((stage==0 && $fell(RBI)) |-> $past(counter) inside {16,27});
  assert property ((stage==1) |-> $stable(RBI));

  // RPHI1 edges allowed only at: stage0: 25(rise), 22/26(fall); stage1: 1(fall)
  assert property ($rose(RPHI1) |-> ($past(stage==0 && counter==25)));
  assert property ($fell(RPHI1) |-> ($past((stage==0 && (counter==22 || counter==26)) || (stage==1 && counter==1))));

  // RPHI2 edges: stage0 rise@28, fall@29; stage1 rise@2, fall@3
  assert property ($rose(RPHI2) |-> ($past((stage==0 && counter==28) || (stage==1 && counter==2))));
  assert property ($fell(RPHI2) |-> ($past((stage==0 && counter==29) || (stage==1 && counter==3))));

  // CS should never fall after it first rises (monotonic high after first assertion)
  assert property (!$fell(CS));

  // 7) Coverage
  // One full stage0 iteration
  cover property (stage==0 && counter==0 ##[1:$] stage==0 && counter==29 ##1 stage==1 && counter==0);
  // Stage1 iterates all the way to 128 then returns to stage0
  cover property (stage==1 && stage_iter==0 && counter==0 ##[1:$]
                  stage==1 && counter==3 && stage_iter==128 ##1 stage==0 && counter==0);
  // Observe all key toggles
  cover property ($rose(RBI));
  cover property ($rose(RPHI1));
  cover property ($rose(RPHI2));
  cover property ($rose(CS));

endmodule

bind rbo_test rbo_test_sva;