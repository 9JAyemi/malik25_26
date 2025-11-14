// SVA for mux_2to1
module mux_2to1_sva (
  input logic sel,
  input logic data_in_0,
  input logic data_in_1,
  input logic out,
  input logic not_sel,
  input logic and0_out,
  input logic and1_out
);

  // Combinational correctness and structural checks (guarded against X on inputs)
  always_comb begin
    if (!$isunknown({sel, data_in_0, data_in_1})) begin
      assert (not_sel   === ~sel);
      assert (and0_out  === (data_in_0 & ~sel));
      assert (and1_out  === (data_in_1 &  sel));
      assert ((and0_out & and1_out) === 1'b0);
      assert (out       === (and0_out | and1_out));
      assert (out       === (sel ? data_in_1 : data_in_0));
      assert (!$isunknown(out));
    end
  end

  // Zero-delay propagation on control and selected data changes
  assert property (@(posedge sel)                    ##0 (out === data_in_1));
  assert property (@(negedge sel)                    ##0 (out === data_in_0));
  assert property (@(posedge data_in_1 or negedge data_in_1) sel  |-> ##0 (out === data_in_1));
  assert property (@(posedge data_in_0 or negedge data_in_0) !sel |-> ##0 (out === data_in_0));

  // Functional coverage (both select states and selected-data transitions)
  cover property (@(posedge sel)                    ##0 (out === data_in_1));
  cover property (@(negedge sel)                    ##0 (out === data_in_0));
  cover property (@(posedge data_in_1) sel   && out);
  cover property (@(negedge data_in_1) sel   && !out);
  cover property (@(posedge data_in_0) !sel  && out);
  cover property (@(negedge data_in_0) !sel  && !out);

  // Input-combination functional coverage
  always_comb begin
    cover (!sel && !data_in_0 && out==0);
    cover (!sel &&  data_in_0 && out==1);
    cover ( sel && !data_in_1 && out==0);
    cover ( sel &&  data_in_1 && out==1);
  end

endmodule

bind mux_2to1 mux_2to1_sva u_mux_2to1_sva (
  .sel(sel),
  .data_in_0(data_in_0),
  .data_in_1(data_in_1),
  .out(out),
  .not_sel(not_sel),
  .and0_out(and0_out),
  .and1_out(and1_out)
);