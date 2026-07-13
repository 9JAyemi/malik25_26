module updown_counter (
    input clk,
    input reset,
    input control,
    output reg [2:0] count
);

    always @(posedge clk or negedge reset) begin
        if (reset == 0) begin
            count <= 3'b0;
        end else begin
            if (control == 0) begin
                count <= count + 1;
            end else begin
                count <= count - 1;
            end
        end
    end

endmodule