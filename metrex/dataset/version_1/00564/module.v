
module regfile(
  input [2:0] addr1,
  input [2:0] addr2,
  input [7:0] data_in,
  output reg [7:0] data_out1,
  output reg [7:0] data_out2,
  input wire write_en
);

  reg [7:0] regs [0:7];
  
  always @(*) begin
    // Read operations
    data_out1 = regs[addr1];
    data_out2 = regs[addr2];
    
    // Write operation
    if (write_en) begin
      regs[addr1] = data_in;
    end
  end
  
endmodule