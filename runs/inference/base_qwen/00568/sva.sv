module alu2_sva(
    input wire clk,
    input wire rst_n,
    input wire [31:0] srca,
    input wire [31:0] srcb,
    input wire [1:0] alucontrol,
    output wire [31:0] aluresult,
    output wire [3:0] aluflags
);
    reg [31:0] sum;
    reg cout;
    wire [31:0] srcbc = ~srcb;

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            sum <= 32'b0;
            cout <= 1'b0;
        end else begin
            if (alucontrol[0]) {cout, sum} = srca + srcbc + 1;
            else {cout, sum} = srca + srcb;
            case (alucontrol)
                2'b00: aluresult <= sum;
                2'b01: aluresult <= sum;
                2'b10: aluresult <= srca & srcb;
                2'b11: aluresult <= srca | srcb;
            endcase
        end
    end

    assign aluflags[3:2] = {aluresult[31], aluresult == 0};
    assign aluflags[1] = cout & ~alucontrol[1];
    assign aluflags[0] = (~(alucontrol[0] ^ srca[31] ^ srca[31])) & (~alucontrol[1]) & (aluresult[31] ^ srca[31]);

    // ALU control signal should be within valid range
    control_signal_valid: assert property (
        @(posedge clk) disable iff (!rst_n) (alucontrol inside {[0:3]})
    );

    // ALU result should be within valid range
    result_valid: assert property (
        @(posedge clk) disable iff (!rst_n) (aluresult inside {[0:4294967295]})
    );

    // ALU flags should be within valid range
    flags_valid: assert property (
        @(posedge clk) disable iff (!rst_n) (aluflags inside {[0:15]})
    );

    // Addition operation should be correct
    addition_correct: assert property (
        @(posedge clk) disable iff (!rst_n) (alucontrol == 2'b00 | alucontrol == 2'b01) |-> (aluresult == srca + srcb)
    );

    // Subtraction operation should be correct
    subtraction_correct: assert property (
        @(posedge clk) disable iff (!rst_n) alucontrol == 2'b00 |-> (aluresult == srca + srcbc + 1)
    );

    // AND operation should be correct
    and_correct: assert property (
        @(posedge clk) disable iff (!rst_n) alucontrol == 2'b10 |-> (aluresult == srca & srcb)
    );

    // OR operation should be correct
    or_correct: assert property (
        @(posedge clk) disable iff (!rst_n) alucontrol == 2'b11 |-> (aluresult == srca | srcb)
    );

    // Zero flag should be set when result is zero
    zero_flag_set: assert property (
        @(posedge clk) disable iff (!rst_n) aluresult == 32'b0 |-> aluflags[2] == 1'b1
    );

    // Negative flag should be set when result is negative
    negative_flag_set: assert property (
        @(posedge clk) disable iff (!rst_n) aluresult[31] == 1'b1 |-> aluflags[3] == 1'b1
    );

    // Carry flag should be set when addition results in carry
    carry_flag_set: assert property (
        @(posedge clk) disable iff (!rst_n) alucontrol == 2'b00 | alucontrol == 2'b01 |-> (aluresult[32] == 1'b1) |-> aluflags[1] == 1'b1
    );

    // Overflow flag should be set when subtraction results in overflow
    overflow_flag_set: assert property (
        @(posedge clk) disable iff (!rst_n) alucontrol == 2'b00 |-> (srca[31] == srcb[31] && aluresult[31] != srca[31]) |-> aluflags[0] == 1'b1
    );

    // Overflow flag should not be set when addition results in overflow
    overflow_flag_not_set: assert property (
        @(posedge clk) disable iff (!rst_n) alucontrol == 2'b00 | alucontrol == 2'b01 |-> (srca[31] != srcb[31] && aluresult[31] == srca[31]) |-> aluflags[0] == 1'b0
    );
endmodule