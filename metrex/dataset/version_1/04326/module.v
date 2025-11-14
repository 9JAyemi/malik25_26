
module clock_gen (
    inclk0,
    c0,
    c1
);

    input    inclk0;
    output   c0;
    output   c1;

    reg    [1:0]    counter;

    assign  c0 = (counter == 2'b00);
    assign  c1 = (counter == 2'b01);

    always @(posedge inclk0) begin
        counter <= counter + 1;
        if (counter == 2'b10)
            counter <= 2'b00;
    end

endmodule
