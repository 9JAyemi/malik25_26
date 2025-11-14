// SVA for CAM (combinational, clockless). Bind into DUT to check behavior concisely.

`ifndef CAM_SVA
`define CAM_SVA

module cam_sva #(parameter int n=8, m=4)
(
  input  logic [n-1:0] data_in,
  input  logic [m-1:0] search_key,
  input  logic         match,
  input  logic [n-1:0] data_out,
  // internal state brought out via bind
  input  logic [n-1:0] stored_data
);

  // Align search_key to stored_data width: zero-extend if m<n, truncate MSBs if m>n
  function automatic logic [n-1:0] align_key(input logic [m-1:0] sk);
    if (m >= n) align_key = sk[m-1 -: n];
    else        align_key = {{(n-m){1'b0}}, sk};
  endfunction

  let expected_match = (align_key(search_key) == stored_data);
  let expected_dout  = expected_match ? stored_data : '0;

  // Functional equivalence (evaluate after combinational settles)
  property p_match_func;
    @(search_key or stored_data or data_in) ##0 (match == expected_match);
  endproperty
  assert property (p_match_func);

  property p_dout_func;
    @(search_key or stored_data or data_in) ##0 (data_out == expected_dout);
  endproperty
  assert property (p_dout_func);

  // Independence from data_in: changing data_in alone must not change outputs
  property p_ignore_data_in;
    @(search_key or stored_data or data_in)
      ( (data_in != $past(data_in)) &&
        (search_key == $past(search_key)) &&
        (stored_data == $past(stored_data)) )
      |-> ##0 (match == $past(match) && data_out == $past(data_out));
  endproperty
  assert property (p_ignore_data_in);

  // Consistency: when match is 1, data_out must equal stored_data; when 0, must be zero
  assert property (@(search_key or stored_data or data_in) ##0 (match |-> data_out == stored_data));
  assert property (@(search_key or stored_data or data_in) ##0 (!match |-> data_out == '0));

  // Clean-inputs => clean-outputs (no X/Z propagation on outputs if inputs are 2-state)
  property p_no_x_out_on_clean_in;
    @(search_key or stored_data or data_in)
      (!$isunknown({search_key, stored_data})) |-> ##0 (!$isunknown({match, data_out}));
  endproperty
  assert property (p_no_x_out_on_clean_in);

  // Flag potential X-optimism: unknown compare inputs should not produce a definitive match=1
  property p_no_true_on_x_inputs;
    @(search_key or stored_data)
      ($isunknown({search_key, stored_data})) |-> ##0 (match !== 1'b1);
  endproperty
  assert property (p_no_true_on_x_inputs);

  // Coverage
  cover property (@(search_key or stored_data) ##0 expected_match);            // hit observed
  cover property (@(search_key or stored_data) ##0 !expected_match);           // miss observed
  cover property (@(search_key or stored_data) (##0 !expected_match ##1 expected_match ##1 !expected_match)); // 0->1->0

endmodule

// Bind into all CAM instances; exposes internal stored_data
bind CAM cam_sva #(.n(n), .m(m)) cam_sva_i (
  .data_in    (data_in),
  .search_key (search_key),
  .match      (match),
  .data_out   (data_out),
  .stored_data(stored_data)
);

`endif