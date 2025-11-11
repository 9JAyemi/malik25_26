module square_wave_generator (
    input clk,
    output reg square_wave
);

    reg [31:0] counter;

    always @(posedge clk) begin
        counter <= counter + 1;
        if (counter == 499_999) begin
            counter <= 0;
            square_wave <= ~square_wave;
        end
    end

endmodule