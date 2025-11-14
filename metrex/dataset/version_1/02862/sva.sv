// SVA for seven_segment_leds_x_8
module seven_segment_leds_x_8_sva (
  input logic                clk,
  input logic [31:0]         bcd_in,
  input logic [7:0]          decimal_points,
  input logic [6:0]          a_to_g,
  input logic                decimal_point,
  input logic [7:0]          anode,
  input logic [2:0]          counter,
  input logic [3:0]          digit,
  input logic [20:0]         clkdiv
);
  default clocking cb @(posedge clk); endclocking
  default disable iff ($isunknown({clk,clkdiv,bcd_in,decimal_points}));

  function automatic logic [6:0] seg_map (input logic [3:0] d);
    case (d)
      4'd0: seg_map = 7'b1000000;
      4'd1: seg_map = 7'b1111001;
      4'd2: seg_map = 7'b0100100;
      4'd3: seg_map = 7'b0110000;
      4'd4: seg_map = 7'b0011001;
      4'd5: seg_map = 7'b0010010;
      4'd6: seg_map = 7'b0000010;
      4'd7: seg_map = 7'b1111000;
      4'd8: seg_map = 7'b0000000;
      4'd9: seg_map = 7'b0010000;
      default: seg_map = 7'b1111111;
    endcase
  endfunction

  // clkdiv increments by 1 after first valid sample
  assert property ( !$past($isunknown(clkdiv)) |-> clkdiv == $past(clkdiv) + 21'd1 );

  // counter derived from clkdiv
  assert property ( counter == clkdiv[20:18] );

  // selected nibble and decimal point
  genvar i;
  generate
    for (i=0; i<8; i++) begin : g_sel
      assert property ( (counter==i) |-> (digit == bcd_in[i*4 +: 4] && decimal_point == ~decimal_points[i]) );
    end
  endgenerate

  // segment encoding equals function of digit
  assert property ( a_to_g == seg_map(digit) );

  // anode is one-hot active-low and matches counter
  assert property ( anode == ~(8'b1 << counter) );
  assert property ( $onehot(~anode) );

  // no X on outputs
  assert property ( !$isunknown({a_to_g, anode, decimal_point}) );

  // Coverage
  generate
    for (i=0; i<8; i++) begin : g_cov_cnt
      cover property ( counter == i );
      cover property ( anode == ~(8'b1 << i) );
    end
  endgenerate

  genvar d;
  generate
    for (d=0; d<=9; d++) begin : g_cov_dig
      cover property ( digit == d[3:0] );
    end
  endgenerate
  cover property ( digit inside {[4'd10:4'd15]} && a_to_g == 7'b1111111 );
  cover property ( decimal_point == 1'b0 );
  cover property ( decimal_point == 1'b1 );
endmodule

bind seven_segment_leds_x_8 seven_segment_leds_x_8_sva sva_i(
  .clk(clk),
  .bcd_in(bcd_in),
  .decimal_points(decimal_points),
  .a_to_g(a_to_g),
  .decimal_point(decimal_point),
  .anode(anode),
  .counter(counter),
  .digit(digit),
  .clkdiv(clkdiv)
);