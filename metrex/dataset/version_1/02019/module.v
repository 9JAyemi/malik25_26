
module binary_counter_with_sync_reset (
    input clk,
    input reset,
    output reg [3:0] Q
);

    always @(posedge clk) begin
        if (reset) begin
            Q <= 4'b0000;
        end else begin
            if (Q == 4'b1111) begin
                Q <= 4'b0000;
            end else begin
                Q <= Q + 1;
            end
        end
    end

endmodule
module shift_register_with_serial_in_out (
    input clk,
    input reset,
    input SI,
    output reg SO,
    output reg [3:0] Q
);

    always @(posedge clk) begin
        if (reset) begin
            Q <= 4'b0000;
        end else begin
            Q <= {Q[2:0], SI};
            SO <= Q[0];
        end
    end

endmodule
module bitwise_OR_module (
    input [3:0] A,
    input [3:0] B,
    output reg [3:0] Y
);

    always @(*) begin
        Y = A | B;
    end

endmodule
module top_module (
    input clk,
    input reset,
    input SI,
    input select,
    output reg [3:0] Q
);

    reg [3:0] counter_out;
    reg [3:0] shift_reg_out;
    reg [3:0] bitwise_OR_out;

    binary_counter_with_sync_reset counter_inst (
        .clk(clk),
        .reset(reset),
        .Q(counter_out)
    );

    shift_register_with_serial_in_out shift_reg_inst (
        .clk(clk),
        .reset(reset),
        .SI(SI),
        .Q(shift_reg_out)
    );

    bitwise_OR_module bitwise_OR_inst (
        .A(counter_out),
        .B(shift_reg_out),
        .Y(bitwise_OR_out)
    );

    always @(posedge clk) begin
        if (reset) begin
            Q <= 4'b0000;
        end else begin
            Q <= bitwise_OR_out;
        end
    end

endmodule