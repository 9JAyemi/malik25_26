
module ECC_memory_block #(
  parameter data_width = 8, // width of the data bus (in bits)
  parameter ecc_width = 4,// width of the error correction code (in bits)
  parameter addr_width = 8 // width of the memory address (in bits)
)(
  input clk,
  input rst,
  input [data_width-1:0] data_in,
  input [addr_width-1:0] addr,
  input we,
  output [data_width-1:0] data_out,
  output [ecc_width-1:0] ecc
);

reg [data_width-1:0] memory [2**addr_width-1:0]; // memory array
reg [ecc_width-1:0] ecc_reg; // error correction code register

// Hamming code generation function
function [ecc_width-1:0] hamming_code;
  input [data_width-1:0] data;
  reg [ecc_width-1:0] ecc;
  integer i;
  begin
    for (i = 0; i < ecc_width; i = i + 1) begin
      ecc[i] = data[i] ^ data[i+1] ^ data[i+3];
    end
    ecc[ecc_width-1] = data[0] ^ data[1] ^ data[2];
    hamming_code = ecc;
  end
endfunction

// Error correction function
function [data_width-1:0] error_correction;
  input [data_width-1:0] data;
  input [ecc_width-1:0] ecc;
  reg [data_width-1:0] corrected_data;
  integer i;
  begin
    for (i = 0; i < data_width; i = i + 1) begin
      corrected_data[i] = data[i] ^ (ecc[0] ^ ecc[1] ^ ecc[3]);
    end
    corrected_data[data_width-1] = data[data_width-1] ^ (ecc[0] ^ ecc[1] ^ ecc[2]);
    error_correction = corrected_data;
  end
endfunction

reg [ecc_width-1:0] ecc_out;
reg [data_width-1:0] corrected_data_out;
// Memory read and write logic
always @(posedge clk) begin
  if (rst) begin
    ecc_reg <= 0;
    ecc_out <= 0;
    corrected_data_out <= 0;
  end
  else if (we) begin
    memory[addr] <= data_in;
    ecc_reg <= hamming_code(data_in);
  end
  else begin
    ecc_out <= hamming_code(memory[addr]);
    corrected_data_out <= memory[addr];
  end
end

// Error detection logic
wire error_detected = ecc_out != ecc_reg;

// Error correction logic
assign data_out = error_detected ? error_correction(corrected_data_out, ecc_reg) : corrected_data_out;

assign ecc = ecc_reg;

endmodule