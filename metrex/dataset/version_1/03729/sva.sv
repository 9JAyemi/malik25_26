// SVA for qrs_refinement1
module qrs_refinement1_sva(
  input  logic [15:0] q_begin_ref,
  input  logic [15:0] s_end_ref,
  input  logic [15:0] q_begin_l3_temp,
  input  logic [15:0] s_end_l3_temp,
  input  logic [15:0] q_begin_l3,
  input  logic [15:0] s_end_l3,
  input  logic        swindow1_full,
  input  logic        qwindow1_full,
  input  logic        s_end_l3_flag,
  input  logic        q_begin_l3_flag,
  input  logic [3:0]  count1,
  input  logic [8:0]  count2,
  input  logic        clk,
  input  logic        nReset
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!nReset);

  // Enable condition
  wire en = (count1 == 4'd2) && (count2 == 9'd1);

  // Async reset clears (check even during reset)
  assert property (@(posedge clk)
                   !nReset |-> (q_begin_ref==16'd0 && s_end_ref==16'd0 &&
                                q_begin_l3_temp==16'd0 && s_end_l3_temp==16'd0));

  // Hold when not enabled
  assert property (!en |=> (q_begin_ref     == $past(q_begin_ref)     &&
                            s_end_ref       == $past(s_end_ref)       &&
                            q_begin_l3_temp == $past(q_begin_l3_temp) &&
                            s_end_l3_temp   == $past(s_end_l3_temp)));

  // q_begin_l3_temp update rules
  assert property (en && (qwindow1_full && q_begin_l3_flag)
                   |=> q_begin_l3_temp == ($signed($past(q_begin_l3)) - 16'sd1));
  assert property (en && !(qwindow1_full && q_begin_l3_flag)
                   |=> q_begin_l3_temp == $past(q_begin_l3_temp));

  // s_end_l3_temp update rules
  assert property (en && (swindow1_full && s_end_l3_flag)
                   |=> s_end_l3_temp == ($signed($past(s_end_l3)) + 16'sd2));
  assert property (en && !(swindow1_full && s_end_l3_flag)
                   |=> s_end_l3_temp == $past(s_end_l3_temp));

  // Reference outputs derive from prior temp values (same-cycle RHS)
  assert property (en |=> q_begin_ref == ($signed($past(q_begin_l3_temp)) <<< 3));
  assert property (en |=> s_end_ref   == ($signed($past(s_end_l3_temp))   <<< 3));

  // Coverage
  cover property (en);
  cover property (en && qwindow1_full && q_begin_l3_flag);
  cover property (en && swindow1_full && s_end_l3_flag);
  cover property (en && !(qwindow1_full && q_begin_l3_flag));
  cover property (en && !(swindow1_full && s_end_l3_flag));
  cover property (en && qwindow1_full && q_begin_l3_flag &&
                       swindow1_full && s_end_l3_flag);
  cover property (en && qwindow1_full && q_begin_l3_flag && q_begin_l3[15]);
  cover property (en && swindow1_full && s_end_l3_flag   && s_end_l3[15]);

endmodule

// Bind example (instantiate once per DUT instance)
// bind qrs_refinement1 qrs_refinement1_sva sva (.*);