module top_module (
    input [3:0] a,
    input [3:0] b,
    input select,
    input CLK,
    input RST,
    input UP,
    input LD,
    input [3:0] D,
    output [3:0] final_output
);

    wire [3:0] binary_sum;
    wire [3:0] counter_output;

    binary_adder binary_adder_inst (
        .a(a),
        .b(b),
        .sum(binary_sum)
    );

    up_down_counter up_down_counter_inst (
        .CLK(CLK),
        .RST(RST),
        .UP(UP),
        .LD(LD),
        .D(D),
        .Q(counter_output)
    );

    assign final_output = select ? counter_output : binary_sum;

endmodule

module binary_adder (
    input [3:0] a,
    input [3:0] b,
    output reg [3:0] sum
);

    always @(*) begin
        sum = a + b;
        if (sum > 15) begin
            sum = sum[3:0];
        end
    end

endmodule

module up_down_counter (
    input CLK,
    input RST,
    input UP,
    input LD,
    input [3:0] D,
    output reg [3:0] Q
);

    always @(posedge CLK) begin
        if (RST) begin
            Q <= 0;
        end else if (UP) begin
            Q <= Q + 1;
        end else if (LD) begin
            Q <= Q - 1;
        end else begin
            Q <= D;
        end
    end

endmodule