// SVA for data_parser: concise, comprehensive, bindable

module data_parser_sva(
  input  logic [3:0] data_in,
  input  logic [1:0] data_out_1,
  input  logic [1:0] data_out_2,
  input  logic       parity
);
  // Use #0 to sample after combinational settling
  always @* begin
    #0;
    // Functional correctness
    assert ({data_out_2, data_out_1} == data_in)
      else $error("data_parser: outputs != input. din=%b dout2=%b dout1=%b", data_in, data_out_2, data_out_1);
    assert (parity == ^data_in)
      else $error("data_parser: parity mismatch. din=%b parity=%b", data_in, parity);

    // No X/Z on outputs when input is known
    if (!$isunknown(data_in)) begin
      assert (!$isunknown({data_out_2, data_out_1, parity}))
        else $error("data_parser: X/Z on outputs with known input. din=%b dout2=%b dout1=%b parity=%b",
                    data_in, data_out_2, data_out_1, parity);
    end
  end

  // Functional coverage: hit all 16 input patterns
  genvar i;
  generate
    for (i = 0; i < 16; i++) begin : COV_IN
      always @* begin
        #0;
        cover (data_in == i[3:0]);
      end
    end
  endgenerate
endmodule

// Bind to DUT
bind data_parser data_parser_sva u_data_parser_sva (.*);