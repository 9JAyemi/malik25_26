module win_blk_mem_gen_prim_width
   (output reg [0:0] douta,
    input clka,
    input [13:0] addra,
    input [0:0] dina,
    input [0:0] wea);

  reg [0:0] mem [0:16383]; // 14-bit addressable memory block

  always @(posedge clka) begin
    if (wea[0]) begin // write operation
      mem[addra] <= dina;
    end else begin // read operation
      douta <= mem[addra];
    end
  end
endmodule