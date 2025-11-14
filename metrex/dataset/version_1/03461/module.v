
module regfile(clk, raddr1, dout1, raddr2, dout2, wr, waddr, din, R1, R2, nrst);
    input           clk;
    input           wr;
    input   [4:0]   raddr1, raddr2, waddr;
    input   [31:0]  din;
    output  [31:0]  dout1, dout2;
    output  [7:0]   R2;
    output  [2:0]   R1;
    input           nrst;

    reg [31:0] mem[0:31];
    reg [31:0] dout1_reg, dout2_reg;
    reg [2:0]  R1_reg;
    reg [7:0]  R2_reg;

    always @(posedge clk or negedge nrst) begin
        if (~nrst) begin
            mem[5'b00001] <= 32'b0;
        end else begin
            if (wr) begin
                mem[waddr] <= din;
            end
            dout1_reg <= mem[raddr1];
            dout2_reg <= mem[raddr2];
            R1_reg <= mem[5'b00001][31:29];
            R2_reg <= mem[4'b0010][7:0];
        end
    end

    assign dout1 = (raddr1 == 5'b0) ? 32'b0 : dout1_reg;
    assign dout2 = (raddr2 == 5'b0) ? 32'b0 : dout2_reg;
    assign R1 = R1_reg;
    assign R2 = R2_reg;

endmodule