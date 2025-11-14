


`ifdef BSV_ASSIGNMENT_DELAY
`else
`define BSV_ASSIGNMENT_DELAY
`endif

module mkRouterOutputArbitersStatic(CLK,
				    RST_N,

				    output_arbs_0_select_requests,
				    output_arbs_0_select,

				    EN_output_arbs_0_next,

				    output_arbs_1_select_requests,
				    output_arbs_1_select,

				    EN_output_arbs_1_next,

				    output_arbs_2_select_requests,
				    output_arbs_2_select,

				    EN_output_arbs_2_next,

				    output_arbs_3_select_requests,
				    output_arbs_3_select,

				    EN_output_arbs_3_next,

				    output_arbs_4_select_requests,
				    output_arbs_4_select,

				    EN_output_arbs_4_next);
  input  CLK;
  input  RST_N;

  input  [4 : 0] output_arbs_0_select_requests;
  output [4 : 0] output_arbs_0_select;

  input  EN_output_arbs_0_next;

  input  [4 : 0] output_arbs_1_select_requests;
  output [4 : 0] output_arbs_1_select;

  input  EN_output_arbs_1_next;

  input  [4 : 0] output_arbs_2_select_requests;
  output [4 : 0] output_arbs_2_select;

  input  EN_output_arbs_2_next;

  input  [4 : 0] output_arbs_3_select_requests;
  output [4 : 0] output_arbs_3_select;

  input  EN_output_arbs_3_next;

  input  [4 : 0] output_arbs_4_select_requests;
  output [4 : 0] output_arbs_4_select;

  input  EN_output_arbs_4_next;

  wire [4 : 0] output_arbs_0_select,
	       output_arbs_1_select,
	       output_arbs_2_select,
	       output_arbs_3_select,
	       output_arbs_4_select;

  assign output_arbs_0_select =
	     { output_arbs_0_select_requests[4],
	       !output_arbs_0_select_requests[4] &&
	       output_arbs_0_select_requests[3],
	       !output_arbs_0_select_requests[4] &&
	       !output_arbs_0_select_requests[3] &&
	       output_arbs_0_select_requests[2],
	       !output_arbs_0_select_requests[4] &&
	       !output_arbs_0_select_requests[3] &&
	       !output_arbs_0_select_requests[2] &&
	       output_arbs_0_select_requests[1],
	       !output_arbs_0_select_requests[4] &&
	       !output_arbs_0_select_requests[3] &&
	       !output_arbs_0_select_requests[2] &&
	       !output_arbs_0_select_requests[1] &&
	       output_arbs_0_select_requests[0] } ;

  assign output_arbs_1_select =
	     { !output_arbs_1_select_requests[0] &&
	       output_arbs_1_select_requests[4],
	       !output_arbs_1_select_requests[0] &&
	       !output_arbs_1_select_requests[4] &&
	       output_arbs_1_select_requests[3],
	       !output_arbs_1_select_requests[0] &&
	       !output_arbs_1_select_requests[4] &&
	       !output_arbs_1_select_requests[3] &&
	       output_arbs_1_select_requests[2],
	       !output_arbs_1_select_requests[0] &&
	       !output_arbs_1_select_requests[4] &&
	       !output_arbs_1_select_requests[3] &&
	       !output_arbs_1_select_requests[2] &&
	       output_arbs_1_select_requests[1],
	       output_arbs_1_select_requests[0] } ;

  assign output_arbs_2_select =
	     { !output_arbs_2_select_requests[1] &&
	       !output_arbs_2_select_requests[0] &&
	       output_arbs_2_select_requests[4],
	       !output_arbs_2_select_requests[1] &&
	       !output_arbs_2_select_requests[0] &&
	       !output_arbs_2_select_requests[4] &&
	       output_arbs_2_select_requests[3],
	       !output_arbs_2_select_requests[1] &&
	       !output_arbs_2_select_requests[0] &&
	       !output_arbs_2_select_requests[4] &&
	       !output_arbs_2_select_requests[3] &&
	       output_arbs_2_select_requests[2],
	       output_arbs_2_select_requests[1],
	       !output_arbs_2_select_requests[1] &&
	       output_arbs_2_select_requests[0] } ;

  assign output_arbs_3_select =
	     { !output_arbs_3_select_requests[2] &&
	       !output_arbs_3_select_requests[1] &&
	       !output_arbs_3_select_requests[0] &&
	       output_arbs_3_select_requests[4],
	       !output_arbs_3_select_requests[2] &&
	       !output_arbs_3_select_requests[1] &&
	       !output_arbs_3_select_requests[0] &&
	       !output_arbs_3_select_requests[4] &&
	       output_arbs_3_select_requests[3],
	       output_arbs_3_select_requests[2],
	       !output_arbs_3_select_requests[2] &&
	       output_arbs_3_select_requests[1],
	       !output_arbs_3_select_requests[2] &&
	       !output_arbs_3_select_requests[1] &&
	       output_arbs_3_select_requests[0] } ;

  assign output_arbs_4_select =
	     { !output_arbs_4_select_requests[3] &&
	       !output_arbs_4_select_requests[2] &&
	       !output_arbs_4_select_requests[1] &&
	       !output_arbs_4_select_requests[0] &&
	       output_arbs_4_select_requests[4],
	       output_arbs_4_select_requests[3],
	       !output_arbs_4_select_requests[3] &&
	       output_arbs_4_select_requests[2],
	       !output_arbs_4_select_requests[3] &&
	       !output_arbs_4_select_requests[2] &&
	       output_arbs_4_select_requests[1],
	       !output_arbs_4_select_requests[3] &&
	       !output_arbs_4_select_requests[2] &&
	       !output_arbs_4_select_requests[1] &&
	       output_arbs_4_select_requests[0] } ;
endmodule  