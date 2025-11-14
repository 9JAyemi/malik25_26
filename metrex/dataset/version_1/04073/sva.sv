// SVA checker for tone_lut32
// Bind or instantiate alongside DUT. Provide a sampling clock/reset.
module tone_lut32_sva (
  input  logic        clk,
  input  logic        rst_n,
  input  logic [5:0]  tone,
  input  logic [15:0] thirty_second_period
);

  function automatic logic [15:0] lut_exp(input logic [5:0] t);
    case (t)
      6'd1 :  lut_exp = 16'd23890; // C3
      6'd2 :  lut_exp = 16'd22549; // C3S
      6'd3 :  lut_exp = 16'd21283; // D3
      6'd4 :  lut_exp = 16'd20089; // D3S
      6'd5 :  lut_exp = 16'd18961; // E3
      6'd6 :  lut_exp = 16'd17897; // F3
      6'd7 :  lut_exp = 16'd16892; // F3S
      6'd8 :  lut_exp = 16'd15944; // G3
      6'd9 :  lut_exp = 16'd15050; // G3S
      6'd10:  lut_exp = 16'd14205; // A3
      6'd11:  lut_exp = 16'd13408; // A3S
      6'd12:  lut_exp = 16'd12655; // B3

      6'd13:  lut_exp = 16'd11945; // C4
      6'd14:  lut_exp = 16'd11275; // C4S
      6'd15:  lut_exp = 16'd10642; // D4
      6'd16:  lut_exp = 16'd10044; // D4S
      6'd17:  lut_exp = 16'd9481;  // E4
      6'd18:  lut_exp = 16'd8949;  // F4
      6'd19:  lut_exp = 16'd8446;  // F4S
      6'd20:  lut_exp = 16'd7972;  // G4
      6'd21:  lut_exp = 16'd7525;  // G4S
      6'd22:  lut_exp = 16'd7103;  // A4
      6'd23:  lut_exp = 16'd6704;  // A4S
      6'd24:  lut_exp = 16'd6328;  // B4

      6'd25:  lut_exp = 16'd5973;  // C5
      6'd26:  lut_exp = 16'd5637;  // C5S
      6'd27:  lut_exp = 16'd5321;  // D5
      6'd28:  lut_exp = 16'd5022;  // D5S
      6'd29:  lut_exp = 16'd4740;  // E5
      6'd30:  lut_exp = 16'd4474;  // F5
      6'd31:  lut_exp = 16'd4223;  // F5S
      6'd32:  lut_exp = 16'd3986;  // G5
      6'd33:  lut_exp = 16'd3763;  // G5S
      6'd34:  lut_exp = 16'd3551;  // A5
      6'd35:  lut_exp = 16'd3352;  // A5S
      6'd36:  lut_exp = 16'd3164;  // B5

      6'd37:  lut_exp = 16'd2986;  // C6
      6'd38:  lut_exp = 16'd2819;  // C6S
      6'd39:  lut_exp = 16'd2661;  // D6
      6'd40:  lut_exp = 16'd2511;  // D6S
      6'd41:  lut_exp = 16'd2370;  // E6
      6'd42:  lut_exp = 16'd2237;  // F6
      6'd43:  lut_exp = 16'd2112;  // F6S
      6'd44:  lut_exp = 16'd1993;  // G6
      6'd45:  lut_exp = 16'd1881;  // G6S
      6'd46:  lut_exp = 16'd1776;  // A6
      6'd47:  lut_exp = 16'd1676;  // A6S
      6'd48:  lut_exp = 16'd1582;  // B6
      default: lut_exp = 16'd0;
    endcase
  endfunction

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // Functional equivalence (main check), ignored while tone is X/Z
  assert property ( !$isunknown(tone) |-> (thirty_second_period == lut_exp(tone)) )
    else $error("tone_lut32: mismatch: tone=%0d got=%0d exp=%0d",
                tone, thirty_second_period, lut_exp(tone));

  // Known input must produce known output
  assert property ( !$isunknown(tone) |-> !$isunknown(thirty_second_period) )
    else $error("tone_lut32: X/Z on output for known tone=%0d", tone);

  // LUT must be strictly decreasing across successive tones (sanity of table)
  generate
    for (genvar k = 1; k < 48; k++) begin : g_monotonic
      initial begin
        if (!(lut_exp(k) > lut_exp(k+1)))
          $error("tone_lut32: LUT not strictly decreasing between %0d and %0d", k, k+1);
      end
    end
  endgenerate

  // Coverage: hit each valid tone mapping and default case
  generate
    for (genvar i = 1; i <= 48; i++) begin : g_cov_valid
      cover property ( (tone == i) && (thirty_second_period == lut_exp(i)) );
    end
  endgenerate
  cover property ( (tone inside {6'd0, [6'd49:6'd63]}) && (thirty_second_period == 16'd0) );

endmodule

// Example bind (connect clk/rst_n from your environment):
// bind tone_lut32 tone_lut32_sva u_tone_lut32_sva (.* , .clk(tb_clk), .rst_n(tb_rst_n));