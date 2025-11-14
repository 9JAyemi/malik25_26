// SVA for barrel_shifter
// Bind into the DUT's scope so we can reference internal signals (stage, reg_file, shifted_data, zero).
module barrel_shifter_sva;

  // Clocking/reset
  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // ---------------- Basic correctness and sequencing ----------------

  // Reset behavior
  a_reset: assert property (@(posedge clk) reset |-> (stage==0 && zero_flag==0));

  // Stage stays in legal range
  a_stage_legal: assert property (stage inside {[0:5]});

  // Stage progression (guard against previous reset)
  a_stage_inc:  assert property (( !$past(reset) && $past(stage)!=5) |-> stage == $past(stage)+1);
  a_stage_wrap: assert property (( !$past(reset) && $past(stage)==5) |-> stage == 0);

  // Combinational behavior per stage
  a_s0: assert property (stage==0 |-> (shifted_data==data_in && reg_file[0]==data_in));
  a_s1: assert property (stage==1 |-> (shifted_data==(reg_file[0] << shift_amount)));
  a_s2: assert property (stage==2 |-> (shifted_data==(reg_file[1] << shift_amount)));
  a_s3: assert property (stage==3 |-> (shifted_data==(reg_file[2] << shift_amount)));
  a_s4: assert property (stage==4 |-> (shifted_data==(reg_file[3] << shift_amount)));
  a_s5_out: assert property (stage==5 |-> (data_out==shifted_data));
  a_s5_zero: assert property (stage==5 |-> (zero == (shifted_data==0) && zero == (data_out==0)));

  // zero_flag updates only on stage 5; otherwise holds value
  a_zf_upd:  assert property (( !$past(reset) && $past(stage)==5) |-> zero_flag == $past(zero));
  a_zf_hold: assert property (( !$past(reset) && stage!=5) |-> zero_flag == $past(zero_flag));

  // Latch-like stability: data_out and reg_file[i] only change when their stage writes them
  a_out_hold: assert property (( !$past(reset) && stage!=5 && $past(stage)!=5) |-> data_out==$past(data_out));
  genvar gi;
  generate
    for (gi=0; gi<5; gi++) begin : g_rf_hold
      a_rf_hold: assert property (( !$past(reset) && stage!=gi && $past(stage)!=gi) |-> reg_file[gi] == $past(reg_file[gi]));
    end
  endgenerate

  // ---------------- End-to-end functional check (under stable shift_amount) ----------------

  function automatic [31:0] sh4(input [31:0] d, input [4:0] s);
    sh4 = (((d<<s)<<s)<<s)<<s;
  endfunction

  sequence s0_to_5;
    stage==0 ##1 stage==1 ##1 stage==2 ##1 stage==3 ##1 stage==4 ##1 stage==5;
  endsequence

  // If shift_amount is stable over the compute window, result equals d << (4*s)
  a_func_out: assert property ( (s0_to_5 and $stable(shift_amount)[*5]) |-> data_out == sh4($past(data_in,5), shift_amount) );
  a_func_zf:  assert property ( (s0_to_5 and $stable(shift_amount)[*5]) |-> ##1 zero_flag == ($past(data_out)==0) );

  // ---------------- Useful coverage ----------------
  c_full_cycle: cover property (s0_to_5);
  c_zf1:        cover property (s0_to_5 ##1 zero_flag);
  c_sa0:        cover property (stage==0 && shift_amount==0 ##5 stage==5 && data_out==data_in);
  c_sa31:       cover property (stage==0 && shift_amount==31 ##5 stage==5);
  c_zero_in:    cover property (stage==0 && data_in==0 ##5 stage==5 && zero_flag);

endmodule

// Bind into all barrel_shifter instances
bind barrel_shifter barrel_shifter_sva bs_sva();