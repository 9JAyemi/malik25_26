module mux4to1 (
  input         clock,
  input         reset,
  input  [7:0]  in_0,
  input  [7:0]  in_1,
  input  [7:0]  in_2,
  input  [7:0]  in_3,
  input  [1:0]  sel,
  output [7:0]  out
);
  reg [7:0] selected_input;
  
  always @ (posedge clock or posedge reset) begin
    if (reset) begin
      selected_input <= 8'b0;
    end else begin
      case (sel)
        2'b00: selected_input <= in_0;
        2'b01: selected_input <= in_1;
        2'b10: selected_input <= in_2;
        2'b11: selected_input <= in_3;
      endcase
    end
  end
  
  assign out = selected_input;
endmodule