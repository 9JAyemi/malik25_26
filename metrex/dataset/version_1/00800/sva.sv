// SVA for TubeROM and TubeController
// Concise, high-quality checks with essential functional coverage

package tube_sva_pkg;
  function automatic logic [6:0] rom_map(logic aux, logic [3:0] val);
    if (aux) begin
      case (val)
        4'h0: rom_map = 7'h00;
        4'h1: rom_map = 7'h73;
        4'h2: rom_map = 7'h78;
        4'h3: rom_map = 7'h50;
        4'h4: rom_map = 7'h1C;
        4'h5: rom_map = 7'h76;
        4'h6: rom_map = 7'h38;
        default: rom_map = 7'h00;
      endcase
    end else begin
      case (val)
        4'h0: rom_map = 7'h3F; 4'h1: rom_map = 7'h06; 4'h2: rom_map = 7'h5B; 4'h3: rom_map = 7'h4F;
        4'h4: rom_map = 7'h66; 4'h5: rom_map = 7'h6D; 4'h6: rom_map = 7'h7D; 4'h7: rom_map = 7'h07;
        4'h8: rom_map = 7'h7F; 4'h9: rom_map = 7'h6F; 4'hA: rom_map = 7'h77; 4'hB: rom_map = 7'h7C;
        4'hC: rom_map = 7'h39; 4'hD: rom_map = 7'h5E; 4'hE: rom_map = 7'h79; 4'hF: rom_map = 7'h71;
        default: rom_map = 7'h00;
      endcase
    end
  endfunction

  function automatic logic [3:0] dig_onehot(logic [1:0] d);
    case (d)
      2'd0: dig_onehot = 4'b0001;
      2'd1: dig_onehot = 4'b0010;
      2'd2: dig_onehot = 4'b0100;
      default: dig_onehot = 4'b1000;
    endcase
  endfunction

  function automatic logic [3:0] select_value(
    logic [1:0] d, logic [3:0] d1, logic [3:0] d2, logic [3:0] d3, logic [3:0] d4
  );
    case (d)
      2'd0: select_value = d1;
      2'd1: select_value = d2;
      2'd2: select_value = d3;
      default: select_value = d4;
    endcase
  endfunction
endpackage

module TubeROM_sva (
  input logic clk,
  input logic [3:0] value,
  input logic       auxValue,
  input logic [6:0] segments
);
  import tube_sva_pkg::*;
  default clocking @(posedge clk); endclocking

  // Functional check
  a_rom_map: assert property (segments == rom_map(auxValue, value));

  // No X/Z on outputs when inputs are known
  a_no_x: assert property (!$isunknown({auxValue, value}) |-> !$isunknown(segments));

  // Coverage: full aux=0 table, aux=1 defined entries, and aux=1 default path
  genvar i;
  generate
    for (i = 0; i < 16; i++) begin : g_cov_aux0
      c_aux0_val: cover property (auxValue == 1'b0 && value == i[3:0]);
    end
    for (i = 0; i < 7; i++) begin : g_cov_aux1
      c_aux1_val: cover property (auxValue == 1'b1 && value == i[3:0]);
    end
  endgenerate
  c_aux1_default: cover property (auxValue == 1'b1 && value >= 4'd7);
endmodule

module TubeController_sva (
  input logic        clk,
  input logic [1:0]  dig,
  input logic [3:0]  dig1,
  input logic [3:0]  dig2,
  input logic [3:0]  dig3,
  input logic [3:0]  dig4,
  input logic [3:0]  dots,
  input logic [3:0]  auxs,
  input logic [3:0]  tubeDig,
  input logic [7:0]  tubeSeg
);
  import tube_sva_pkg::*;
  default clocking @(posedge clk); endclocking

  // tubeDig correctness and one-hot
  a_onehot: assert property ($onehot(tubeDig) && tubeDig == dig_onehot(dig));

  // tubeSeg correctness (dot + ROM map of selected digit with selected aux)
  a_tubeSeg: assert property (
    tubeSeg == { dots[dig], rom_map(auxs[dig], select_value(dig, dig1, dig2, dig3, dig4)) }
  );

  // No X/Z on outputs when inputs are known
  a_no_x: assert property (
    !$isunknown({dig, dig1, dig2, dig3, dig4, dots, auxs}) |-> !$isunknown({tubeDig, tubeSeg})
  );

  // Coverage: exercise digit selection, dot, aux default path when aux=1 and value>=7
  c_dig0: cover property (dig == 2'd0);
  c_dig1: cover property (dig == 2'd1);
  c_dig2: cover property (dig == 2'd2);
  c_dig3: cover property (dig == 2'd3);
  c_dot1: cover property (dots[dig] == 1'b1);
  c_dot0: cover property (dots[dig] == 1'b0);
  c_aux1_default: cover property (auxs[dig] == 1'b1 && select_value(dig, dig1, dig2, dig3, dig4) >= 4'd7);
endmodule

// Example binds (connect an appropriate clock from your environment):
// bind TubeROM       TubeROM_sva       rom_chk  (.clk(clk), .value(value), .auxValue(auxValue), .segments(segments));
// bind TubeController TubeController_sva ctrl_chk (.clk(clk), .dig(dig), .dig1(dig1), .dig2(dig2), .dig3(dig3), .dig4(dig4),
//                                                  .dots(dots), .auxs(auxs), .tubeDig(tubeDig), .tubeSeg(tubeSeg));