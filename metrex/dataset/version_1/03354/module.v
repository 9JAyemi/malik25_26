
module input_fifo_blk_mem_gen_generic_cstr #(
    parameter WIDTH = 8,
    DEPTH = 256
) (
    input [WIDTH-1:0] D,
    input clk,
    input WEA,
    input tmp_ram_rd_en,
    input srst,
    output reg [WIDTH-1:0] Q,
    output reg [9:0] gc0_count_d1_reg,
    input [WIDTH-1:0] din
);

localparam ADDR_WIDTH = $clog2(DEPTH);

reg [WIDTH-1:0] mem [0:DEPTH-1];
reg [ADDR_WIDTH-1:0] head = 0;
reg [ADDR_WIDTH-1:0] tail = 0;

always @ (posedge clk) begin
    if (srst) begin
        head <= 0;
        tail <= 0;
    end else begin
        if (WEA && (head != tail || gc0_count_d1_reg == 0)) begin
            mem[head] <= WEA;
            head <= head + 1;
        end
        if (tmp_ram_rd_en && head != tail) begin
            tail <= tail + 1;
            Q <= mem[tail-1]; // mem[tail-1] should be used instead of din here
        end
    end
end

always @ (posedge clk) begin
    if (srst) begin
       gc0_count_d1_reg <= 0;
    end
    else if (WEA && (head != tail || gc0_count_d1_reg == 0)) begin
        gc0_count_d1_reg <= gc0_count_d1_reg + 1; // Moved here
    end
    if (tmp_ram_rd_en && head != tail) begin
        gc0_count_d1_reg <= gc0_count_d1_reg - 1; // Moved here
    end
end

endmodule