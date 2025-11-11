// SVA for v468a05 / v468a05_v9a2a06
// Focused, concise checks + coverage for functional correctness and wiring

// Bind these in your testbench (shown at bottom).

module v468a05_xor8_sva (
  input  logic [31:0] i,
  input  logic [7:0]  o0,
  input  logic [7:0]  o1,
  input  logic [7:0]  o2,
  input  logic [7:0]  o3
);
  // LSB constants used by DUT
  localparam logic [7:0] C0 = 8'h12;
  localparam logic [7:0] C1 = 8'h56;
  localparam logic [7:0] C2 = 8'h39;
  localparam logic [7:0] C3 = 8'hBC;

  // Purely combinational functional checks
  always_comb begin
    // Functional mapping (lower byte XOR)
    assert (o0 === (i[7:0] ^ C0)) else $error("o0 != i[7:0]^12");
    assert (o1 === (i[7:0] ^ C1)) else $error("o1 != i[7:0]^56");
    assert (o2 === (i[7:0] ^ C2)) else $error("o2 != i[7:0]^39");
    assert (o3 === (i[7:0] ^ C3)) else $error("o3 != i[7:0]^BC");

    // Cross-consistency (all decode back to same i[7:0])
    assert (((o0 ^ C0) === (o1 ^ C1)) &&
            ((o1 ^ C1) === (o2 ^ C2)) &&
            ((o2 ^ C2) === (o3 ^ C3)) &&
            ((o3 ^ C3) === i[7:0]))
      else $error("Cross-consistency failed");

    // No X/Z on outputs when input LSBs are known
    if (!$isunknown(i[7:0])) begin
      assert (!$isunknown(o0)) else $error("o0 X/Z with known input");
      assert (!$isunknown(o1)) else $error("o1 X/Z with known input");
      assert (!$isunknown(o2)) else $error("o2 X/Z with known input");
      assert (!$isunknown(o3)) else $error("o3 X/Z with known input");
    end
  end

  // Independence from upper bits (i[31:8] must not affect outputs)
  logic [31:0] i_prev;
  logic [7:0]  o0_prev, o1_prev, o2_prev, o3_prev;
  initial begin
    i_prev   = 'x;
    o0_prev  = 'x;
    o1_prev  = 'x;
    o2_prev  = 'x;
    o3_prev  = 'x;
  end

  // Event-driven temporal checks without a clock
  always @(i or o0 or o1 or o2 or o3) begin
    if (i_prev !== 'x) begin
      // Upper bits change alone -> outputs must remain unchanged
      if ((i[7:0] === i_prev[7:0]) && (i[31:8] !== i_prev[31:8])) begin
        assert (o0 === o0_prev && o1 === o1_prev && o2 === o2_prev && o3 === o3_prev)
          else $error("Outputs changed due to i[31:8] only");
        cover (1); // observed independence scenario
      end
      // Lower bits change -> at least one output changes
      if (i[7:0] !== i_prev[7:0]) begin
        assert ((o0 !== o0_prev) || (o1 !== o1_prev) || (o2 !== o2_prev) || (o3 !== o3_prev))
          else $error("Outputs did not respond to i[7:0] change");
        cover (1); // observed responsiveness
      end
    end

    // Basic functional coverage
    if (!$isunknown(i[7:0])) begin
      cover (i[7:0] == 8'h00);
      cover (i[7:0] == 8'hFF);
      cover (i[7:0] == C0 && o0 == 8'h00);
      cover (i[7:0] == C1 && o1 == 8'h00);
      cover (i[7:0] == C2 && o2 == 8'h00);
      cover (i[7:0] == C3 && o3 == 8'h00);
      cover (o0 == 8'h00); // each output hits 0 at least once
      cover (o1 == 8'h00);
      cover (o2 == 8'h00);
      cover (o3 == 8'h00);
    end

    // Update snapshot
    i_prev  = i;
    o0_prev = o0;
    o1_prev = o1;
    o2_prev = o2;
    o3_prev = o3;
  end
endmodule

// Bind to both the implementation and the top to also catch port-wiring issues.
bind v468a05_v9a2a06 v468a05_xor8_sva sva_impl (
  .i(i), .o0(o0), .o1(o1), .o2(o2), .o3(o3)
);
bind v468a05 v468a05_xor8_sva sva_top (
  .i(ve841af), .o0(vdd0469), .o1(vf93ecb), .o2(v4ba85d), .o3(vc6471a)
);