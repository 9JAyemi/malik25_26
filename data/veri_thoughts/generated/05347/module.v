module flag_gen(clk, rst, full, emptyp, wr_en, rd_en);
  input clk, rst, wr_en, rd_en;
  output full, emptyp;
  reg full, emptyp;
  reg [4:0] count;
  parameter max_count=5'b01111;
  
  always @ (posedge clk or negedge rst) begin
    if(!rst) count <= 0;
    else begin
      case({wr_en, rd_en})
        2'b00: count <= count;
        2'b01: if(count !== 5'b00000) count <= count - 1;
        2'b10: if(count !== max_count) count <= count + 1;
        2'b11: count <= count;
      endcase
    end
  end
  
  always @ (count) begin
    if(count == 5'b00000) emptyp <= 1;
    else emptyp <= 0;
  end
  
  always @ (count) begin
    if(count == max_count) full <= 1;
    else full <= 0;
  end
endmodule