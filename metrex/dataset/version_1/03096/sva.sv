// SVA for Mux_3x1_bv2
// Bind to the DUT type; no DUT edits required.

module Mux_3x1_bv2_sva #(parameter W=32)
(
  input  logic [1:0]      select,
  input  logic [W-1:0]    ch_0,
  input  logic [W-1:0]    ch_1,
  input  logic [W-1:0]    ch_2,
  input  logic [W-1:0]    data_out
);
  logic [W-1:0] exp;

  // Combinational mirror of DUT behavior (including default on X/Z select)
  always @* begin
    unique casez (select)
      2'b00: exp = {W{1'b0}};
      2'b01: exp = ch_0;
      2'b10: exp = ch_1;
      2'b11: exp = ch_2;
      default: exp = ch_0; // mirrors DUT default on X/Z
    endcase
  end

  // Functional equivalence (deferred to end-of-timestep to avoid NBA races)
  always @* begin
    assert #0 (data_out === exp)
      else $error("Mux_3x1_bv2: data_out != expected for select=%b", select);
  end

  // Sanity: select must be known (avoid implicit default on X/Z)
  always @* begin
    assert #0 (!$isunknown(select))
      else $error("Mux_3x1_bv2: select has X/Z");
  end

  // Sanity: if all inputs known, output must be known
  always @* begin
    if (!$isunknown({select, ch_0, ch_1, ch_2})) begin
      assert #0 (!$isunknown(data_out))
        else $error("Mux_3x1_bv2: data_out has X/Z with known inputs");
    end
  end

  // Compact functional coverage
  always @* begin
    cover #0 (select == 2'b00 && data_out === {W{1'b0}});
    cover #0 (select == 2'b01 && data_out === ch_0);
    cover #0 (select == 2'b10 && data_out === ch_1);
    cover #0 (select == 2'b11 && data_out === ch_2);
  end
endmodule

bind Mux_3x1_bv2 Mux_3x1_bv2_sva #(.W(W)) mux3x1_bv2_sva_i (
  .select(select),
  .ch_0(ch_0),
  .ch_1(ch_1),
  .ch_2(ch_2),
  .data_out(data_out)
);