
module top_module (
    input clk,
    input reset,
    input [3:0] load,
    input [3:0] A,
    input [3:0] B,
    input Cin,
    output reg [3:0] q
);

    wire [3:0] adder_out;
    wire [3:0] counter_out;
    wire [3:0] subtract_out;

    ripple_carry_adder adder_inst (
        .A(A),
        .B(B),
        .Cin(Cin),
        .S(adder_out)
    );

    synchronous_counter counter_inst (
        .clk(clk),
        .reset(reset),
        .load(load),
        .q(counter_out)
    );

    subtractor subtract_inst (
        .A(adder_out),
        .B(counter_out),
        .q(subtract_out)
    );

    always @(*) begin
        q = subtract_out;
    end

endmodule
module ripple_carry_adder (
    input [3:0] A,
    input [3:0] B,
    input Cin,
    output [3:0] S
);

    wire [3:0] sum;

    full_adder fa0 (
        .A(A[0]),
        .B(B[0]),
        .Cin(Cin),
        .S(sum[0])
    );

    full_adder fa1 (
        .A(A[1]),
        .B(B[1]),
        .Cin(sum[0]),
        .S(sum[1])
    );

    full_adder fa2 (
        .A(A[2]),
        .B(B[2]),
        .Cin(sum[1]),
        .S(sum[2])
    );

    full_adder fa3 (
        .A(A[3]),
        .B(B[3]),
        .Cin(sum[2]),
        .S(sum[3])
    );

    assign S = sum;

endmodule
module full_adder (
    input A,
    input B,
    input Cin,
    output S
);

    assign S = A ^ B ^ Cin;

endmodule
module synchronous_counter (
    input clk,
    input reset,
    input [3:0] load,
    output reg [3:0] q
);

    always @(posedge clk) begin
        if (reset) begin
            q <= 4'b0;
        end else if (load) begin
            q <= load;
        end else begin
            q <= q + 1;
        end
    end

endmodule
module subtractor (
    input [3:0] A,
    input [3:0] B,
    output reg [3:0] q
);

    always @(*) begin
        q = A - B;
    end

endmodule