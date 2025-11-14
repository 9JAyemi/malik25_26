module FSM #(
  parameter n = 4, // number of input signals
  parameter m = 2 // number of output signals
)(
  input [n-1:0] in,
  input clk,
  output reg [m-1:0] out
);

parameter s = 8; // number of states

reg [s-1:0] state; // current state
reg [s-1:0] next_state; // next state
reg [m-1:0] output_reg; // output register

// transition table
function [s-1:0] transition_table;
  input [n-1:0] input_signals;
  begin
    case (input_signals)
      4'b0000: transition_table = 3'b000;
      4'b0001: transition_table = 3'b001;
      4'b0010: transition_table = 3'b010;
      4'b0011: transition_table = 3'b011;
      4'b0100: transition_table = 3'b100;
      4'b0101: transition_table = 3'b101;
      4'b0110: transition_table = 3'b110;
      4'b0111: transition_table = 3'b111;
      4'b1000: transition_table = 3'b000;
      4'b1001: transition_table = 3'b001;
      4'b1010: transition_table = 3'b010;
      4'b1011: transition_table = 3'b011;
      4'b1100: transition_table = 3'b100;
      4'b1101: transition_table = 3'b101;
      4'b1110: transition_table = 3'b110;
      4'b1111: transition_table = 3'b111;
    endcase
  end
endfunction

// output table
function [m-1:0] output_table;
  input [n-1:0] input_signals;
  begin
    case (input_signals)
      4'b0000: output_table = 2'b00;
      4'b0001: output_table = 2'b01;
      4'b0010: output_table = 2'b10;
      4'b0011: output_table = 2'b11;
      4'b0100: output_table = 2'b00;
      4'b0101: output_table = 2'b01;
      4'b0110: output_table = 2'b10;
      4'b0111: output_table = 2'b11;
      4'b1000: output_table = 2'b00;
      4'b1001: output_table = 2'b01;
      4'b1010: output_table = 2'b10;
      4'b1011: output_table = 2'b11;
      4'b1100: output_table = 2'b00;
      4'b1101: output_table = 2'b01;
      4'b1110: output_table = 2'b10;
      4'b1111: output_table = 2'b11;
    endcase
  end
endfunction

// compute next state and output
always @(*) begin
  next_state = transition_table(in);
  output_reg = output_table(in);
end

// assign output and update state
always @(posedge clk) begin
  state <= next_state;
  out <= output_reg;
end

endmodule