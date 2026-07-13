module pulse_generator (
    input clk,
    output reg pulse
);

reg [6:0] counter = 0; // counter for counting clock cycles

always @(posedge clk) begin
    counter <= counter + 1; // increment counter on every clock cycle
    if(counter == 100) begin
        pulse <= 1; // set pulse output high when counter reaches 100
    end
    if(counter == 110) begin
        pulse <= 0; // reset pulse output low after 10 clock cycles
        counter <= 0; // reset counter
    end
end

endmodule