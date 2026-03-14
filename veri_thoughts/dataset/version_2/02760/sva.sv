module mux_2to1_behavioral_sva (
  input logic [3:0] a,
  input logic [3:0] b,
  input logic       s,
  input logic [3:0] mux_out
);

  // On any input edge, mux_out equals selected input based on s.
  check_function_on_input_edges: assert property (
    @(posedge s or negedge s
      or posedge a[0] or negedge a[0]
      or posedge a[1] or negedge a[1]
      or posedge a[2] or negedge a[2]
      or posedge a[3] or negedge a[3]
      or posedge b[0] or negedge b[0]
      or posedge b[1] or negedge b[1]
      or posedge b[2] or negedge b[2]
      or posedge b[3] or negedge b[3])
    ((s == 1'b0) && (mux_out == a)) || ((s == 1'b1) && (mux_out == b))
  );

  // On select rising edge, mux_out must equal b.
  check_out_follows_b_on_s_rise: assert property (
    @(posedge s) mux_out == b
  );

  // On select falling edge, mux_out must equal a.
  check_out_follows_a_on_s_fall: assert property (
    @(negedge s) mux_out == a
  );

  // With s=0, any change on a must be reflected on mux_out.
  check_a_change_reflected_when_s0: assert property (
    @(posedge a[0] or negedge a[0]
      or posedge a[1] or negedge a[1]
      or posedge a[2] or negedge a[2]
      or posedge a[3] or negedge a[3])
    (s == 1'b0) |-> (mux_out == a)
  );

  // With s=1, any change on b must be reflected on mux_out.
  check_b_change_reflected_when_s1: assert property (
    @(posedge b[0] or negedge b[0]
      or posedge b[1] or negedge b[1]
      or posedge b[2] or negedge b[2]
      or posedge b[3] or negedge b[3])
    (s == 1'b1) |-> (mux_out == b)
  );

  // On any change of mux_out, it must equal the currently selected input.
  check_out_is_consistent_on_out_change: assert property (
    @(posedge mux_out[0] or negedge mux_out[0]
      or posedge mux_out[1] or negedge mux_out[1]
      or posedge mux_out[2] or negedge mux_out[2]
      or posedge mux_out[3] or negedge mux_out[3])
    ((s == 1'b0) && (mux_out == a)) || ((s == 1'b1) && (mux_out == b))
  );

endmodule