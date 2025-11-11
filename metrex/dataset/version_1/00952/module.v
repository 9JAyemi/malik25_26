module top_module (
    input clk,
    input reset,   // Synchronous active-high reset
    input a,b,c,   // Binary inputs for the decoder module
    output [7:0] q // 8-bit final output from the functional module
);

    // Instantiate the decoder module
    decoder_3to4 decoder_inst(
        .a(a),
        .b(b),
        .c(c),
        .w(q[3]),
        .x(q[2]),
        .y(q[1]),
        .z(q[0])
    );

    // Instantiate the counter module
    counter_4bit counter_inst(
        .clk(clk),
        .reset(reset),
        .q3(q[7]),
        .q2(q[6]),
        .q1(q[5]),
        .q0(q[4])
    );

endmodule

// 3-to-4 decoder module
module decoder_3to4 (
    input a,
    input b,
    input c,
    output w,
    output x,
    output y,
    output z
);

    assign w = ~(a & b & c);
    assign x = ~(a & b & ~c);
    assign y = ~(a & ~b & c);
    assign z = ~(a & ~b & ~c);

endmodule

// 4-bit binary counter module
module counter_4bit (
    input clk,
    input reset,   // Synchronous active-high reset
    output reg q3,
    output reg q2,
    output reg q1,
    output reg q0
);

    always @(posedge clk) begin
        if (reset) begin
            q3 <= 0;
            q2 <= 0;
            q1 <= 0;
            q0 <= 0;
        end else begin
            if (q0 == 0 && q1 == 0 && q2 == 0 && q3 == 0) begin
                q0 <= 1;
            end else if (q0 == 1 && q1 == 0 && q2 == 0 && q3 == 0) begin
                q0 <= 0;
                q1 <= 1;
            end else if (q0 == 0 && q1 == 1 && q2 == 0 && q3 == 0) begin
                q0 <= 1;
                q1 <= 0;
            end else if (q0 == 1 && q1 == 1 && q2 == 0 && q3 == 0) begin
                q0 <= 0;
                q1 <= 1;
            end else if (q0 == 0 && q1 == 0 && q2 == 1 && q3 == 0) begin
                q0 <= 1;
                q1 <= 0;
                q2 <= 0;
            end else if (q0 == 1 && q1 == 0 && q2 == 1 && q3 == 0) begin
                q0 <= 0;
                q1 <= 1;
                q2 <= 0;
            end else if (q0 == 0 && q1 == 1 && q2 == 1 && q3 == 0) begin
                q0 <= 1;
                q1 <= 0;
                q2 <= 0;
            end else if (q0 == 1 && q1 == 1 && q2 == 1 && q3 == 0) begin
                q0 <= 0;
                q1 <= 0;
                q2 <= 1;
            end else if (q0 == 0 && q1 == 0 && q2 == 0 && q3 == 1) begin
                q0 <= 1;
                q1 <= 0;
                q2 <= 0;
                q3 <= 0;
            end else if (q0 == 1 && q1 == 0 && q2 == 0 && q3 == 1) begin
                q0 <= 0;
                q1 <= 1;
                q2 <= 0;
                q3 <= 0;
            end else if (q0 == 0 && q1 == 1 && q2 == 0 && q3 == 1) begin
                q0 <= 1;
                q1 <= 0;
                q2 <= 0;
                q3 <= 0;
            end else if (q0 == 1 && q1 == 1 && q2 == 0 && q3 == 1) begin
                q0 <= 0;
                q1 <= 0;
                q2 <= 1;
                q3 <= 0;
            end else if (q0 == 0 && q1 == 0 && q2 == 1 && q3 == 1) begin
                q0 <= 1;
                q1 <= 0;
                q2 <= 0;
                q3 <= 0;
            end else if (q0 == 1 && q1 == 0 && q2 == 1 && q3 == 1) begin
                q0 <= 0;
                q1 <= 1;
                q2 <= 0;
                q3 <= 0;
            end else if (q0 == 0 && q1 == 1 && q2 == 1 && q3 == 1) begin
                q0 <= 1;
                q1 <= 0;
                q2 <= 0;
                q3 <= 0;
            end else if (q0 == 1 && q1 == 1 && q2 == 1 && q3 == 1) begin
                q0 <= 0;
                q1 <= 0;
                q2 <= 0;
                q3 <= 0;
            end
        end
    end

endmodule