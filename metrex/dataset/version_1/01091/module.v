module wait_generator(
    input clk, nreset, WAIT,
    output reg wait_random
);

    reg [8:0] wait_counter;

    always @(posedge clk or negedge nreset) begin
        if (!nreset) begin
            wait_counter <= 9'b0;
        end else begin
            wait_counter <= wait_counter + 1'b1;
        end
    end

    always @* begin
        if (WAIT) begin
            if (wait_counter[5:0] != 6'b0) begin
                wait_random = 1'b1;
            end else begin
                wait_random = 1'b0;
            end
        end else begin
            wait_random = 1'b0;
        end
    end

endmodule