module binary_counter (
    // Inputs
    reset,
    clk,
    // Outputs
    count_out
);

    // Input signals
    input reset;
    input clk;

    // Output signals
    output [3:0] count_out;

    // Internal signals
    reg [3:0] count;

    always @(posedge clk or negedge reset) begin
        if (!reset) begin
            count <= 4'b0;
        end else begin
            if (count == 4'b1111) begin
                count <= 4'b0;
            end else begin
                count <= count + 1;
            end
        end
    end

    assign count_out = count;

endmodule