// SVA for add_sub_4bit – concise, high-quality checks and coverage

module add_sub_4bit_sva (
  input logic        CK,
  input logic [3:0]  A, B,
  input logic        sub,
  input logic [3:0]  Y,
  input logic        Cout,

  // internal signals
  input logic [3:0]  B_neg,
  input logic [3:0]  B_sub,
  input logic [4:0]  Y_add,
  input logic [3:0]  Y_reg
);

  default clocking cb @(posedge CK); endclocking

  bit past_valid;
  initial past_valid = 1'b0;
  always @(posedge CK) past_valid <= 1'b1;

  function automatic [4:0] f_sum (input logic [3:0] a_i, b_i, input logic sub_i);
    logic [3:0] bsel;
    begin
      bsel  = sub_i ? (~b_i + 4'd1) : b_i;
      f_sum = {1'b0, a_i} + {1'b0, bsel};
    end
  endfunction

  // Structural/combinational correctness
  ap_bneg:              assert property (B_neg == (~B + 4'd1));
  ap_bsub_sel:          assert property (B_sub == (sub ? B_neg : B));
  ap_yadd:              assert property (Y_add == ({1'b0, A} + {1'b0, B_sub}));
  ap_y_equals_reg:      assert property (Y == Y_reg);
  ap_cout_equals_yadd:  assert property (Cout == Y_add[4]);

  // Functional correctness (timing-aware)
  ap_y_correct:         assert property (disable iff (!past_valid)
                                         Y == $past(f_sum(A,B,sub)[3:0]));
  ap_cout_correct:      assert property (Cout == f_sum(A,B,sub)[4]);

  // Meaning of Cout in add/sub modes
  ap_sub_borrow_meaning: assert property (sub  |-> (Cout == (A >= B))); // no borrow => Cout=1
  ap_add_carry_meaning:  assert property (!sub |-> (Cout == ((A + B) >= 5'd16)));

  // No X/Z after first clock
  ap_no_x_in:  assert property (disable iff (!past_valid) !$isunknown({A,B,sub}));
  ap_no_x_out: assert property (disable iff (!past_valid) !$isunknown({Y,Cout}));

  // Y must only change on posedge CK
  ap_y_stable_negedge: assert property (@(negedge CK) $stable(Y));
  ap_yreg_stable_negedge: assert property (@(negedge CK) $stable(Y_reg));

  // Coverage
  cover_add_no_carry:  cover property (!sub && !Cout);
  cover_add_carry:     cover property (!sub &&  Cout);
  cover_sub_no_borrow: cover property ( sub &&  Cout && (A>=B));
  cover_sub_borrow:    cover property ( sub && !Cout && (A< B));
  cover_equal_sub:     cover property ( sub && (A==B));
  cover_zero_zero:     cover property (!sub && (A==4'd0) && (B==4'd0));
  cover_max_max_add:   cover property (!sub && (A==4'hF) && (B==4'hF) && Cout);
  cover_sub_toggle:    cover property (disable iff (!past_valid) $changed(sub));

endmodule

bind add_sub_4bit add_sub_4bit_sva sva (.*);