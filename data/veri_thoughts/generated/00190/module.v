
module small_fifo_cntr (
    input aclr,       // Asynchronous clear input
    input clock,      // Clock input
    input cnt_en,     // Counter enable input
    input updown,     // Up/down counter select input
    output [2:0] q,   // Counter output
    input sclr        // Synchronous clear input
);

    // Internal registers
    reg [2:0] q_reg;

    // Counter logic
    always @ (posedge clock or posedge aclr) begin
        if (aclr) begin
            q_reg <= 3'b0;
        end else if (sclr) begin
            q_reg <= 3'b0;
        end else if (cnt_en) begin
            if (updown) begin
                q_reg <= q_reg + 1'b1;
            end else begin
                q_reg <= q_reg - 1'b1;
            end
        end
    end

    // Output assignment
    assign q = q_reg;

endmodule
