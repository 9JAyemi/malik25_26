
module mux_parity (
  input [2:0] sel,
  input [3:0] data0,
  input [3:0] data1,
  input [3:0] data2,
  input [3:0] data3,
  input [3:0] data4,
  input [3:0] data5,
  output [3:0] out,
  output parity
);

  wire [3:0] mux_out [0:5];
  wire [2:0] sel_dec [0:7];
  
  // Generate intermediate signals for each input data
  assign mux_out[0] = (sel_dec[0]) ? data0 : 4'b0;
  assign mux_out[1] = (sel_dec[1]) ? data1 : 4'b0;
  assign mux_out[2] = (sel_dec[2]) ? data2 : 4'b0;
  assign mux_out[3] = (sel_dec[3]) ? data3 : 4'b0;
  assign mux_out[4] = (sel_dec[4]) ? data4 : 4'b0;
  assign mux_out[5] = (sel_dec[5]) ? data5 : 4'b0;
  
  // Generate select signals using a 3-to-8 decoder
  assign sel_dec[0] = (sel == 3'b000);
  assign sel_dec[1] = (sel == 3'b001);
  assign sel_dec[2] = (sel == 3'b010);
  assign sel_dec[3] = (sel == 3'b011);
  assign sel_dec[4] = (sel == 3'b100);
  assign sel_dec[5] = (sel == 3'b101);
  assign sel_dec[6] = 1'b0;
  assign sel_dec[7] = 1'b0;
  
  // Select the active input data using an 8-input OR gate
  assign out = mux_out[0] | mux_out[1] | mux_out[2] | mux_out[3] | mux_out[4] | mux_out[5];
  
  // Generate the parity bit using an XOR gate
  assign parity = out[0] ^ out[1] ^ out[2] ^ out[3];
  
endmodule
