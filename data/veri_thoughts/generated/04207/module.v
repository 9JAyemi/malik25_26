module pulse_generator (
    input clk,
    input d,
    output reg q
);

    // Local signals
    wire buf_q;
    wire xor_out;
    reg q_temp;

    // D flip-flop
    always @(posedge clk) begin
        q_temp <= d;
    end

    assign buf_q = q_temp;

    // XOR gate to compare current and previous input signals
    assign xor_out = buf_q ^ d;

    // Generate pulse whenever input signal changes from 0 to 1
    always @(posedge clk) begin
        if (d == 1 && xor_out == 1) begin
            q <= 1;
        end else begin
            q <= 0;
        end
    end

endmodule