module signal_converter_sva (
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic C1,
    output logic X
);
    // The logic is purely combinational as there are no sequential elements.

    // Voltage supply signals are always driven, so no assertions needed for them.

    // X is a function of A1, A2, A3, B1, and C1
    // X = (A1 & A2 & A3) | (A1 & A2 & B1) | (A1 & A2 & C1) | (A1 & A3 & B1) | (A1 & A3 & C1) | (A1 & B1 & C1) | (A2 & A3 & B1) | (A2 & A3 & C1) | (A2 & B1 & C1) | (A3 & B1 & C1)
    // This can be simplified to X = A1 & (A2 | B1 | C1) | A2 & (A3 | B1 | C1) | A3 & (B1 | C1)
    // However, for simplicity, we will assert the full expression.

    // X should be 1 if any of the conditions are met
    always_comb begin
        X = (A1 & A2 & A3) | (A1 & A2 & B1) | (A1 & A2 & C1) | (A1 & A3 & B1) | (A1 & A3 & C1) | (A1 & B1 & C1) | (A2 & A3 & B1) | (A2 & A3 & C1) | (A2 & B1 & C1) | (A3 & B1 & C1);
    end

    // Assert that X is 1 if any of the conditions are met
    always @(posedge clk) begin
        assert property (
            disable iff (!reset_n) X == ((A1 & A2 & A3) | (A1 & A2 & B1) | (A1 & A2 & C1) | (A1 & A3 & B1) | (A1 & A3 & C1) | (A1 & B1 & C1) | (A2 & A3 & B1) | (A2 & A3 & C1) | (A2 & B1 & C1) | (A3 & B1 & C1))
        ) else $error("X is not 1 when any of the conditions are met");
    end

    // Assert that X is 0 if none of the conditions are met
    always @(posedge clk) begin
        assert property (
            disable iff (!reset_n) X == 0 |-> !((A1 & A2 & A3) | (A1 & A2 & B1) | (A1 & A2 & C1) | (A1 & A3 & B1) | (A1 & A3 & C1) | (A1 & B1 & C1) | (A2 & A3 & B1) | (A2 & A3 & C1) | (A2 & B1 & C1) | (A3 & B1 & C1))
        ) else $error("X is 1 when none of the conditions are met");
    end

    // Assert that X is always 1 if A1 is 1
    always @(posedge clk) begin
        assert property (
            disable iff (!reset_n) A1 |-> X == 1
        ) else $error("X is not 1 when A1 is 1");
    end

    // Assert that X is always 0 if A1 is 0 and none of the other conditions are met
    always @(posedge clk) begin
        assert property (
            disable iff (!reset_n) A1 == 0 |-> !((A2 & A3 & B1) | (A2 & A3 & C1) | (A2 & B1 & C1) | (A3 & B1 & C1)) |-> X == 0
        ) else $error("X is 1 when A1 is 0 and none of the other conditions are met");
    end

    // Assert that X is always 1 if A2 is 1
    always @(posedge clk) begin
        assert property (
            disable iff (!reset_n) A2 |-> X == 1
        ) else $error("X is not 1 when A2 is 1");
    end

    // Assert that X is always 0 if A2 is 0 and none of the other conditions are met
    always @(posedge clk) begin
        assert property (
            disable iff (!reset_n) A2 == 0 |-> !((A1 & A3 & B1) | (A1 & A3 & C1) | (A1 & B1 & C1) | (A3 & B1 & C1)) |-> X == 0
        ) else $error("X is 1 when A2 is 0 and none of the other conditions are met");
    end

    // Assert that X is always 1 if A3 is 1
    always @(posedge clk) begin
        assert property (
            disable iff (!reset_n) A3 |-> X == 1
        ) else $error("X is not 1 when A3 is 1");
    end

    // Assert that X is always 0 if A3 is 0 and none of the other conditions are met
    always @(posedge clk) begin
        assert property (
            disable iff (!reset_n) A3 == 0 |-> !((A1 & A2 & B1) | (A1 & A2 & C1) | (A1 & B1 & C1) | (A2 & B1 & C1)) |-> X == 0
        ) else $error("X is 1 when A3 is 0 and none of the other conditions are met");
    end

    // Assert that X is always 1 if B1 is 1
    always @(posedge clk) begin
        assert property (
            disable iff (!reset_n) B1 |-> X == 1
        ) else $error("X is not 1 when B1 is 1");
    end

    // Assert that X is always 0 if B1 is 0 and none of the other conditions are met
    always @(posedge clk) begin
        assert property (
            disable iff (!reset_n) B1 == 0 |-> !((A1 & A2 & A3) | (A1 & A2 & C1) | (A1 & A3 & C1) | (A2 & A3 & C1) | (A2 & A3 & A1) | (A3 & A1 & C1)) |-> X == 0
        ) else $error("X is 1 when B1 is 0 and none of the other conditions are met");
    end

    // Assert that X is always 1 if C1 is 1
    always @(posedge clk) begin
        assert property (
            disable iff (!reset_n) C1 |-> X == 1
        ) else $error("X is not 1 when C1 is 1");
    end

    // Assert that X is always 0 if C1 is 0 and none of the other conditions are met
    always @(posedge clk) begin
        assert property (
            disable iff (!reset_n) C1 == 0 |-> !((A1 & A2 & A3) | (A1 & A2 & B1) | (A1 & A3 & B1) | (A2 & A3 & B1) | (A2 & A3 & A1) | (A3 & A1 & B1)) |-> X == 0
        ) else $error("X is 1 when C1 is 0 and none of the other conditions are met");
    end
endmodule