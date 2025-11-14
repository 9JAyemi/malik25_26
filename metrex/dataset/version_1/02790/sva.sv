// SVA checker for SSEG_Driver
module SSEG_Driver_sva;

  // Use DUT signals directly via bind-in scope
  default clocking cb @(posedge clk); endclocking

  localparam int Nbits = $bits(q_reg);
  wire [1:0] q_sel = q_reg[Nbits-1 -: 2];

  // 7-seg encoding function (must match DUT)
  function automatic logic [6:0] enc (input logic [3:0] h);
    case (h)
      4'h0: enc = 7'b1000000; 4'h1: enc = 7'b1111001; 4'h2: enc = 7'b0100100; 4'h3: enc = 7'b0110000;
      4'h4: enc = 7'b0011001; 4'h5: enc = 7'b0010010; 4'h6: enc = 7'b0000010; 4'h7: enc = 7'b1111000;
      4'h8: enc = 7'b0000000; 4'h9: enc = 7'b0010000; 4'hA: enc = 7'b0001000; 4'hB: enc = 7'b0000011;
      4'hC: enc = 7'b1000110; 4'hD: enc = 7'b0100001; 4'hE: enc = 7'b0000110; 4'hF: enc = 7'b0001110;
      default: enc = 7'b1111111;
    endcase
  endfunction

  // Reset and counter behavior
  a_reset_clears: assert property (reset |-> q_reg == '0);
  a_count_inc:    assert property (disable iff (reset) q_reg == $past(q_reg) + 1);
  a_qnext:        assert property (disable iff (reset) ##0 (q_next == q_reg + 1));

  // an legality: exactly one active-low digit
  a_an_onecold:   assert property (disable iff (reset) $onehot(~an));

  // Mux correctness (forward: q_sel -> an,hex_in)
  a_sel00_fwd:    assert property (disable iff (reset) (q_sel==2'b00) |-> ##0 (an==4'b1110 && hex_in==data[3:0]));
  a_sel01_fwd:    assert property (disable iff (reset) (q_sel==2'b01) |-> ##0 (an==4'b1101 && hex_in==data[7:4]));
  a_sel10_fwd:    assert property (disable iff (reset) (q_sel==2'b10) |-> ##0 (an==4'b1011 && hex_in==data[11:8]));
  a_sel11_fwd:    assert property (disable iff (reset) (q_sel==2'b11) |-> ##0 (an==4'b0111 && hex_in==data[15:12]));

  // Mux correctness (reverse: an -> q_sel,hex_in)
  a_sel00_rev:    assert property (disable iff (reset) (an==4'b1110) |-> ##0 (q_sel==2'b00 && hex_in==data[3:0]));
  a_sel01_rev:    assert property (disable iff (reset) (an==4'b1101) |-> ##0 (q_sel==2'b01 && hex_in==data[7:4]));
  a_sel10_rev:    assert property (disable iff (reset) (an==4'b1011) |-> ##0 (q_sel==2'b10 && hex_in==data[11:8]));
  a_sel11_rev:    assert property (disable iff (reset) (an==4'b0111) |-> ##0 (q_sel==2'b11 && hex_in==data[15:12]));

  // Decoder correctness
  a_decode:       assert property (disable iff (reset) ##0 (sseg == enc(hex_in)));

  // End-to-end: selected digit encodes the corresponding data nibble
  a_e2e0:         assert property (disable iff (reset) (an==4'b1110) |-> ##0 (sseg == enc(data[3:0])));
  a_e2e1:         assert property (disable iff (reset) (an==4'b1101) |-> ##0 (sseg == enc(data[7:4])));
  a_e2e2:         assert property (disable iff (reset) (an==4'b1011) |-> ##0 (sseg == enc(data[11:8])));
  a_e2e3:         assert property (disable iff (reset) (an==4'b0111) |-> ##0 (sseg == enc(data[15:12])));

  // No unreachable default pattern when not in reset
  a_no_default:   assert property (disable iff (reset) sseg != 7'b1111111);

  // Knownness (no X/Z) after reset deasserted
  a_known:        assert property (disable iff (reset) !$isunknown({q_reg, q_next, hex_in, an, sseg}));

  // Coverage
  c_each_sel0:    cover  property (disable iff (reset) (q_sel==2'b00 && an==4'b1110));
  c_each_sel1:    cover  property (disable iff (reset) (q_sel==2'b01 && an==4'b1101));
  c_each_sel2:    cover  property (disable iff (reset) (q_sel==2'b10 && an==4'b1011));
  c_each_sel3:    cover  property (disable iff (reset) (q_sel==2'b11 && an==4'b0111));

  covergroup cg_hex @(posedge clk);
    option.per_instance = 1;
    hex_val: coverpoint hex_in iff(!reset) { bins all_vals[] = {[0:15]}; }
    an_sel:  coverpoint an     iff(!reset) { bins s0={4'b1110}; bins s1={4'b1101}; bins s2={4'b1011}; bins s3={4'b0111}; }
  endgroup
  cg_hex cg = new();

endmodule

bind SSEG_Driver SSEG_Driver_sva sva_i();