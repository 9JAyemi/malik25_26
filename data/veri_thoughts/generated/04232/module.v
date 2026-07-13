
module pll(
    input wire refclk,
    input wire rst,
    output wire outclk_0,
    output wire outclk_1,
    output wire locked
);

    // PLL parameters
    parameter N = 10;
    parameter M = 2;
    parameter P = 2;

    // PLL state
    reg [N-1:0] phase_accumulator = 0;
    reg outclk_0_reg = 0;
    reg outclk_1_reg = 0;
    reg locked_reg = 0;

    // PLL logic
    always @(posedge refclk or posedge rst) begin
        if (rst) begin
            phase_accumulator <= 0;
            outclk_0_reg <= 0;
            outclk_1_reg <= 0;
            locked_reg <= 0;
        end else begin
            phase_accumulator <= phase_accumulator + 1;
            if (phase_accumulator == (N-1)) begin
                phase_accumulator <= 0;
                outclk_0_reg <= ~outclk_0_reg;
                outclk_1_reg <= ~outclk_1_reg;
                locked_reg <= 1;
            end
        end
    end

    // Output assignments
    assign outclk_0 = outclk_0_reg;
    assign outclk_1 = outclk_1_reg;
    assign locked = locked_reg;

endmodule

module clk_generator(
    input wire refclk,
    input wire rst,
    output wire outclk_0,
    output wire outclk_1,
    output wire locked
);

    // PLL instantiation
    pll pll_i (
        .refclk(refclk),
        .rst(rst),
        .outclk_0(outclk_0),
        .outclk_1(outclk_1),
        .locked(locked)
    );

endmodule

module top(
    input wire clk,
    input wire rst,
    output wire out
);

    wire outclk_0;
    wire outclk_1;
    wire locked;

    clk_generator clk_gen (
        .refclk(clk),
        .rst(rst),
        .outclk_0(outclk_0),
        .outclk_1(outclk_1),
        .locked(locked)
    );

    assign out = outclk_0;

endmodule
