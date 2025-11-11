module memory_generator
  #(parameter MEM_DEPTH = 1024,
            INIT_VECTOR = 256'h0000000000000000000000000000000000000000000000000000000000000000)
  (
    output reg [35:0] douta,
    input wire clka,
    input wire [9:0] addra,
    input wire en,
    input wire [35:0] data_in
  );

  reg [35:0] mem [0:MEM_DEPTH-1];

  // Initialize memory with INIT_VECTOR
  integer i;
  initial begin
    for (i=0; i<MEM_DEPTH; i=i+1) begin
      mem[i] = INIT_VECTOR;
    end
  end

  always @(posedge clka) begin
    douta <= mem[addra];
    if (en) begin
      mem[addra] <= data_in;
    end
  end

endmodule