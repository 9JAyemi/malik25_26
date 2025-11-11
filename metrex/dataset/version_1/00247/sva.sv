// Bindable SVA for ad_datafmt.
// Focuses on correctness of pass-through vs. 1-cycle pipelined data formatting,
// MSB XOR behavior, sign-extension, and X-propagation. Includes compact coverage.

module ad_datafmt_sva #(
  parameter int DATA_WIDTH = 16,
  parameter bit DISABLE    = 0
) (
  input  logic                  clk,
  input  logic                  valid,
  input  logic [DATA_WIDTH-1:0] data,
  input  logic                  dfmt_enable,
  input  logic                  dfmt_type,
  input  logic                  dfmt_se,
  input  logic                  valid_out,
  input  logic [15:0]           data_out
);

  // Basic param sanity (compile/elab-time)
  initial begin
    if (DATA_WIDTH < 1 || DATA_WIDTH > 16) $error("ad_datafmt: DATA_WIDTH must be 1..16");
  end

  // Helpers to compute expected results
  function automatic logic [15:0] fmt16(
    input logic [DATA_WIDTH-1:0] din,
    input logic en, ty, se
  );
    logic [15:0] out;
    logic type_s, sign_s;

    type_s = en & ty;
    out    = '0;
    if (DATA_WIDTH >= 2) out[DATA_WIDTH-2:0] = din[DATA_WIDTH-2:0];
    out[DATA_WIDTH-1] = type_s ^ din[DATA_WIDTH-1];

    if (DATA_WIDTH < 16) begin
      sign_s = (en & se) & (type_s ^ din[DATA_WIDTH-1]);
      out[15:DATA_WIDTH] = {(16-DATA_WIDTH){sign_s}};
    end
    return out;
  endfunction

  function automatic logic [15:0] zext16(input logic [DATA_WIDTH-1:0] din);
    logic [15:0] out;
    out = '0;
    if (DATA_WIDTH <= 16) out[DATA_WIDTH-1:0] = din;
    return out;
  endfunction

  // Past-valid for $past usage (no reset in DUT)
  logic past_valid;
  always_ff @(posedge clk) past_valid <= 1'b1;

  // X-propagation checks (always)
  property p_no_x_out;
    @(posedge clk) !$isunknown({valid_out, data_out});
  endproperty
  assert property (p_no_x_out) else $error("ad_datafmt: X/Z detected on outputs");

  generate
    if (DISABLE) begin : g_disable

      // Combinational pass-through (sampled each clk edge)
      property p_disable_passthrough;
        @(posedge clk) (valid_out == valid) && (data_out == zext16(data));
      endproperty
      assert property (p_disable_passthrough)
        else $error("ad_datafmt: DISABLE=1 passthrough mismatch");

      // Some lightweight coverage
      cover property (@(posedge clk) valid_out && valid && data_out == zext16(data));

    end else begin : g_enable

      // 1-cycle pipeline on valid
      property p_latency_valid;
        @(posedge clk) past_valid |-> (valid_out == $past(valid));
      endproperty
      assert property (p_latency_valid)
        else $error("ad_datafmt: valid_out != $past(valid)");

      // 1-cycle pipeline on formatted data
      property p_latency_data;
        @(posedge clk) past_valid |-> (data_out == $past(fmt16(data, dfmt_enable, dfmt_type, dfmt_se)));
      endproperty
      assert property (p_latency_data)
        else $error("ad_datafmt: data_out != $past(formatted data)");

      // MSB XOR behavior (independent assertion for clarity)
      property p_msb_xor;
        @(posedge clk) past_valid |-> (data_out[DATA_WIDTH-1] ==
          ($past(dfmt_enable & dfmt_type) ^ $past(data[DATA_WIDTH-1])));
      endproperty
      assert property (p_msb_xor)
        else $error("ad_datafmt: MSB XOR behavior violated");

      // Lower bits pass-through unchanged
      if (DATA_WIDTH > 1) begin
        property p_lowbits_passthrough;
          @(posedge clk) past_valid |-> (data_out[DATA_WIDTH-2:0] == $past(data[DATA_WIDTH-2:0]));
        endproperty
        assert property (p_lowbits_passthrough)
          else $error("ad_datafmt: lower bits not passed through");
      end

      // Sign extension correctness when DATA_WIDTH < 16
      if (DATA_WIDTH < 16) begin
        property p_signext;
          @(posedge clk) past_valid |-> (
            data_out[15:DATA_WIDTH] ==
            { (16-DATA_WIDTH){ ($past(dfmt_enable & dfmt_se) &
                                ($past(dfmt_enable & dfmt_type) ^ $past(data[DATA_WIDTH-1]))) } }
          );
        endproperty
        assert property (p_signext)
          else $error("ad_datafmt: sign extension incorrect");
      end

      // Compact functional coverage
      // - Observe both 0/1 MSB cases under formatting
      cover property (@(posedge clk) past_valid && dfmt_enable && data[DATA_WIDTH-1]==0);
      cover property (@(posedge clk) past_valid && dfmt_enable && data[DATA_WIDTH-1]==1);
      // - Exercise XOR path
      cover property (@(posedge clk) past_valid && dfmt_enable && dfmt_type);
      // - Exercise sign-extension effect
      if (DATA_WIDTH < 16)
        cover property (@(posedge clk) past_valid && dfmt_enable && dfmt_se && data[DATA_WIDTH-1]);

      // - Observe valid toggle and pipeline relationship
      cover property (@(posedge clk) past_valid && $rose(valid) && ##1 valid_out);
      cover property (@(posedge clk) past_valid && $fell(valid) && ##1 !valid_out);

    end
  endgenerate

endmodule

// Example bind into DUT (instantiate once in your testbench or a package):
// bind ad_datafmt ad_datafmt_sva #(.DATA_WIDTH(DATA_WIDTH), .DISABLE(DISABLE)) ad_datafmt_sva_i (.*);