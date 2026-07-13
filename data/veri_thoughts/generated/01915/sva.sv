module regfile_sva (
    input logic [2:0] addr1,
    input logic [2:0] addr2,
    input logic [7:0] data_in,
    input logic [7:0] data_out1,
    input logic [7:0] data_out2,
    input logic write_en
);
    // When both read addresses are equal, both outputs must match (sampled on write_en rising edge).
    check_equal_outputs_on_we_rise: assert property (
        @(posedge write_en) (addr1 == addr2) |-> (data_out1 == data_out2)
    );

    // When both read addresses are equal, both outputs must match (sampled on write_en falling edge).
    check_equal_outputs_on_we_fall: assert property (
        @(negedge write_en) (addr1 == addr2) |-> (data_out1 == data_out2)
    );
endmodule