module binary_counter (
    input clk,
    input reset,
    output reg [3:0] count
);

    reg [3:0] next_count;
    reg [3:0] curr_count;

    always @ (posedge clk) begin
        if (reset) begin
            curr_count <= 4'b0000;
            count <= curr_count;
        end else begin
            next_count <= curr_count + 4'b0001;
            curr_count <= next_count;
            count <= curr_count;
        end
    end

endmodule