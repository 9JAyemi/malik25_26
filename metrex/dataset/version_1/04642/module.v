
module top_module(
    input wire clk,
    input wire rst,
    input wire [7:0] in_hi,
    input wire [7:0] in_lo,
    output wire [15:0] out,
    output wire parity_bit );

    reg [7:0] in_hi_reg;
    reg [7:0] in_lo_reg;
    reg [15:0] out_reg;
    reg parity_bit_reg;

    wire [15:0] out_wire;
    wire parity_bit_wire;

    // Pipeline stage 1
    always @(posedge clk) begin
        if (rst) begin
            in_hi_reg <= 8'b0;
            in_lo_reg <= 8'b0;
        end else begin
            in_hi_reg <= in_hi;
            in_lo_reg <= in_lo;
        end
    end

    // Pipeline stage 2
    always @(posedge clk) begin
        if (rst) begin
            out_reg <= 16'b0;
            parity_bit_reg <= 1'b0;
        end else begin
            out_reg <= {in_hi_reg, in_lo_reg};
            parity_bit_reg <= in_hi_reg ^ in_lo_reg;
        end
    end

    // Pipeline stage 3
    assign out_wire = out_reg;
    assign parity_bit_wire = parity_bit_reg;

    assign out = out_wire;
    assign parity_bit = parity_bit_wire;

endmodule