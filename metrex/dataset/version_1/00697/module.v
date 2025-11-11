
module top_module (
    input clk,
    input reset,
    input SER_IN,
    input SH_EN,
    output reg [7:0] q
);

    // Instantiate the 4-bit counter module
    wire [3:0] counter;
    counter_module counter_inst (
        .clk(clk),
        .reset(reset),
        .q(counter)
    );

    // Instantiate the 4-bit shift register module
    wire [3:0] shift_reg;
    shift_register_module shift_reg_inst (
        .clk(clk),
        .SER_IN(SER_IN),
        .SH_EN(SH_EN),
        .reset(reset),
        .q(shift_reg)
    );

    // Combine the counter and shift register outputs into an 8-bit output
    always @(*) begin
        q = {counter, shift_reg};
    end

endmodule
module counter_module (
    input clk,
    input reset,
    output reg [3:0] q
);

    always @(posedge clk) begin
        if (reset) begin
            q <= 4'b0000;
        end else begin
            q <= q + 1'b1;
        end
    end

endmodule
module shift_register_module (
    input clk,
    input SER_IN,
    input SH_EN,
    input reset,
    output reg [3:0] q
);

    always @(posedge clk) begin
        if (reset) begin
            q <= 4'b0000;
        end else if (SH_EN) begin
            q <= {q[2:0], SER_IN};
        end
    end

endmodule