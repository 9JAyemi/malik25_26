module majority_counter (
    input clk,
    input reset,
    input enable,
    input A, B, C, D,
    output reg [7:0] final_output
);

    wire Y;
    wire [3:0] counter_out;
    wire [1:0] counter_out_even;

    majority_gate majority_gate_inst (
        .A(A),
        .B(B),
        .C(C),
        .D(D),
        .Y(Y)
    );

    counter counter_inst (
        .clk(clk),
        .reset(reset),
        .enable(enable),
        .out(counter_out)
    );

    always @ (posedge clk or posedge reset) begin
        if (reset) begin
            final_output <= 0;
        end else if (enable) begin
            if (counter_out[0] == 1) begin
                final_output <= counter_out;
            end else begin
                final_output <= Y;
            end
        end
    end

    assign counter_out_even = counter_out[0] ? counter_out[1:0] : counter_out[2:1];

endmodule

module majority_gate (
    input A, B, C, D,
    output Y
);

    assign Y = (A & B & C) | (A & B & D) | (A & C & D) | (B & C & D);

endmodule

module counter (
    input clk,
    input reset,
    input enable,
    output reg [3:0] out
);

    always @ (posedge clk or posedge reset) begin
        if (reset) begin
            out <= 0;
        end else if (enable) begin
            out <= out + 1;
        end
    end

endmodule