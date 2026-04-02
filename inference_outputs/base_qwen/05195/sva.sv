module twos_complement_sva (
    input logic [3:0] a,
    output logic [3:0] twos_comp
);
    // Combinational logic, clocked assertions
    // Calculate the one's complement of a
    ones_comp: assert property (
        @(posedge CLK) disable iff (!RESETn) (ones_comp == ~a)
    );
    // Calculate the inverted value by adding 1 to the one's complement
    inverted: assert property (
        @(posedge CLK) disable iff (!RESETn) (inverted == ones_comp + 4'b1)
    );
    // Calculate the two's complement by adding 1 if the most significant bit is 1
    add_one: assert property (
        @(posedge CLK) disable iff (!RESETn) (add_one == (inverted[3] ? inverted + 4'b1 : inverted))
    );
    // The output twos_comp should be equal to the calculated add_one
    twos_comp_out: assert property (
        @(posedge CLK) disable iff (!RESETn) (twos_comp == add_one)
    );
endmodule