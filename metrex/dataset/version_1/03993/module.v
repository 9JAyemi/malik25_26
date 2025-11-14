`define DATA_WIDTH 32 

module dual_port_mem(
    input clk,
    input r_en1,
    input [1:0] r_addr1,
    input r_en2,
    input [1:0] r_addr2,
    input w_en,
    input [1:0] w_addr,
    input [2*(`DATA_WIDTH+1)-1:0] w_data,
    output reg [2*(`DATA_WIDTH+1)-1:0] r_data1,
    output reg [2*(`DATA_WIDTH+1)-1:0] r_data2
);

    reg [2*(`DATA_WIDTH+1)-1:0] mem [0:3];

    always @(posedge clk) begin
        if (r_en1 && r_en2) begin
            r_data1 <= mem[r_addr1];
            r_data2 <= mem[r_addr2];
        end else if (r_en1) begin
            r_data1 <= mem[r_addr1];
            r_data2 <= 0;
        end else if (r_en2) begin
            r_data1 <= 0;
            r_data2 <= mem[r_addr2];
        end

        if (w_en) begin
            mem[w_addr] <= w_data;
        end
    end

endmodule