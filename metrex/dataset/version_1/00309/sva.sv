// SVA for DisplayCtrl. Bind this file to the DUT.
module DisplayCtrl_sva(
  input  logic [26:0] Clk,
  input  logic        reset,
  input  logic [15:0] memoryData,
  input  logic        An0, An1, An2, An3,
  input  logic        Ca, Cb, Cc, Cd, Ce, Cf, Cg, Dp
);
  default clocking cb @(posedge Clk[0]); endclocking

  // 7-seg decode function (active-low segments)
  function automatic logic [6:0] hex7(input logic [3:0] h);
    case (h)
      4'h0: hex7 = 7'b0000001; 4'h1: hex7 = 7'b1001111;
      4'h2: hex7 = 7'b0010010; 4'h3: hex7 = 7'b0000110;
      4'h4: hex7 = 7'b1001100; 4'h5: hex7 = 7'b0100100;
      4'h6: hex7 = 7'b0100000; 4'h7: hex7 = 7'b0001111;
      4'h8: hex7 = 7'b0000000; 4'h9: hex7 = 7'b0000100;
      4'hA: hex7 = 7'b0001000; 4'hB: hex7 = 7'b1100000;
      4'hC: hex7 = 7'b0110001; 4'hD: hex7 = 7'b1000010;
      4'hE: hex7 = 7'b0110000; 4'hF: hex7 = 7'b0111000;
      default: hex7 = 7'hx;
    endcase
  endfunction

  wire [6:0] cats = {Ca,Cb,Cc,Cd,Ce,Cf,Cg};
  wire       a = Clk[19];
  wire       b = Clk[18];

  // Basic IO correctness
  a_dp_high:      assert property (disable iff (reset) Dp == 1'b1);
  a_no_x_io:      assert property (disable iff (reset) !$isunknown({An0,An1,An2,An3,Ca,Cb,Cc,Cd,Ce,Cf,Cg,Dp}));
  a_an_onehot:    assert property (disable iff (reset) $onehot(~{An3,An2,An1,An0}));

  // Anode decode from scan clock bits
  a_an0_map:      assert property (disable iff (reset) An0 == ( a |  b));
  a_an1_map:      assert property (disable iff (reset) An1 == ( a | ~b));
  a_an2_map:      assert property (disable iff (reset) An2 == (~a |  b));
  a_an3_map:      assert property (disable iff (reset) An3 == (~a | ~b));

  // Cathode decode must match selected nibble
  a_mux_00:       assert property (disable iff (reset) (~a & ~b) |-> cats == hex7(memoryData[3:0]));
  a_mux_01:       assert property (disable iff (reset) (~a &  b) |-> cats == hex7(memoryData[7:4]));
  a_mux_10:       assert property (disable iff (reset) ( a & ~b) |-> cats == hex7(memoryData[11:8]));
  a_mux_11:       assert property (disable iff (reset) ( a &  b) |-> cats == hex7(memoryData[15:12]));

  // Cathodes always one of the valid encodings
  a_cats_valid:   assert property (disable iff (reset)
                      cats inside {
                        7'b0000001,7'b1001111,7'b0010010,7'b0000110,
                        7'b1001100,7'b0100100,7'b0100000,7'b0001111,
                        7'b0000000,7'b0000100,7'b0001000,7'b1100000,
                        7'b0110001,7'b1000010,7'b0110000,7'b0111000
                      });

  // Coverage: every digit position and value appears
  c_scan00:       cover property (disable iff (reset) (~a & ~b) && !An0 && cats == hex7(memoryData[3:0]));
  c_scan01:       cover property (disable iff (reset) (~a &  b) && !An1 && cats == hex7(memoryData[7:4]));
  c_scan10:       cover property (disable iff (reset) ( a & ~b) && !An2 && cats == hex7(memoryData[11:8]));
  c_scan11:       cover property (disable iff (reset) ( a &  b) && !An3 && cats == hex7(memoryData[15:12]));

  genvar i;
  generate
    for (i=0; i<16; i++) begin : G_COV_HEX
      c_hex: cover property (disable iff (reset) cats == hex7(i[3:0]));
    end
  endgenerate
endmodule

bind DisplayCtrl DisplayCtrl_sva sva_inst(.*);