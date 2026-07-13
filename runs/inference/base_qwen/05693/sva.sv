module shift_register_sva (
    input logic clk,
    input logic load,
    input logic [3:0] data_in,
    output logic [3:0] data_out
);
    // Sequential logic: data_out is updated on the rising edge of clk
    // When load is high, data_out is loaded with data_in
    // When load is low, data_out is shifted right by one bit
    shift_register_property: assert property (
        @(posedge clk) disable iff (!load) (data_out == {data_out[2:0], data_out[3]})
    ) else $error("Shift register did not shift right as expected");

    // Sequential logic: data_out is updated on the rising edge of clk
    // When load is high, data_out is loaded with data_in
    load_property: assert property (
        @(posedge clk) disable iff (!load) (data_out == data_in)
    ) else $error("Shift register did not load with data_in as expected");

    // Sequential logic: data_out is updated on the rising edge of clk
    // When load is low, data_out is shifted right by one bit
    shift_property: assert property (
        @(posedge clk) disable iff (!load) (data_out[3] == data_out[2])
    ) else $error("Shift register did not shift right as expected");

    // Sequential logic: data_out is updated on the rising edge of clk
    // When load is high, data_out is loaded with data_in
    load_data_property: assert property (
        @(posedge clk) disable iff (!load) (data_out[0] == data_in[3])
    ) else $error("Shift register did not load with data_in as expected");

    // Sequential logic: data_out is updated on the rising edge of clk
    // When load is low, data_out is shifted right by one bit
    shift_data_property: assert property (
        @(posedge clk) disable iff (!load) (data_out[2] == data_out[1])
    ) else $error("Shift register did not shift right as expected");

    // Sequential logic: data_out is updated on the rising edge of clk
    // When load is high, data_out is loaded with data_in
    load_data_property_2: assert property (
        @(posedge clk) disable iff (!load) (data_out[1] == data_in[2])
    ) else $error("Shift register did not load with data_in as expected");

    // Sequential logic: data_out is updated on the rising edge of clk
    // When load is low, data_out is shifted right by one bit
    shift_data_property_2: assert property (
        @(posedge clk) disable iff (!load) (data_out[0] == data_in[1])
    ) else $error("Shift register did not shift right as expected");

    // Sequential logic: data_out is updated on the rising edge of clk
    // When load is high, data_out is loaded with data_in
    load_data_property_3: assert property (
        @(posedge clk) disable iff (!load) (data_out[3] == data_in[0])
    ) else $error("Shift register did not load with data_in as expected");

    // Sequential logic: data_out is updated on the rising edge of clk
    // When load is low, data_out is shifted right by one bit
    shift_data_property_3: assert property (
        @(posedge clk) disable iff (!load) (data_out[2] == data_in[0])
    ) else $error("Shift register did not shift right as expected");

    // Sequential logic: data_out is updated on the rising edge of clk
    // When load is low, data_out is shifted right by one bit
    shift_data_property_4: assert property (
        @(posedge clk) disable iff (!load) (data_out[1] == data_in[0])
    ) else $error("Shift register did not shift right as expected");

    // Sequential logic: data_out is updated on the rising edge of clk
    // When load is low, data_out is shifted right by one bit
    shift_data_property_5: assert property (
        @(posedge clk) disable iff (!load) (data_out[0] == data_in[0])
    ) else $error("Shift register did not shift right as expected");
endmodule