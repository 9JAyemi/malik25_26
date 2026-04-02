module reverse_bit_order_sva (
    input logic clk,
    input logic [99:0] in,
    output logic [99:0] out
);
    reg [99:0] shift_reg;
    wire [99:0] reversed;

    assign reversed[0] = shift_reg[99];
    genvar i;
    generate
        for (i = 1; i < 100; i = i + 1) begin : SHIFT_LOOP
            assign reversed[i] = shift_reg[99-i];
        end
    endgenerate

    assign out = reversed;

    always @(posedge clk) begin
        shift_reg <= {shift_reg[98:0], in[0]};
    end

    ///// Shift register behavior /////
    // Shift register should shift left on each clock edge.
    shift_reg_behavior: assert property (
        @(posedge clk) disable iff (!clk) shift_reg[99] == in[0]
    );

    ///// Reversed output behavior /////
    // Reversed output should correctly reflect the shift register.
    reversed_output_behavior: assert property (
        @(posedge clk) disable iff (!clk) out == reversed
    );

    ///// Initial state /////
    // Initial state of shift register should be all zeros.
    initial begin
        @(posedge clk) disable iff (!clk) assert(shift_reg == 100'b0);
    end

    ///// Edge detection /////
    // Edge detection on shift register should be correct.
    edge_detection: assert property (
        @(posedge clk) disable iff (!clk) $rose(shift_reg[99]) |-> shift_reg[99] == 1'b1
    );

    // Additional properties can be added here as needed.
endmodule