module StepDecoder(output [15:0] TimeSteps, input [3:0]StepCounter);
		
		and and1(TimeSteps[0], ~StepCounter[3], ~StepCounter[2], ~StepCounter[1], ~StepCounter[0]);
		and and2(TimeSteps[1], ~StepCounter[3], ~StepCounter[2], ~StepCounter[1], StepCounter[0]);
		and and3(TimeSteps[2], ~StepCounter[3], ~StepCounter[2], StepCounter[1], ~StepCounter[0]);
		and and4(TimeSteps[3], ~StepCounter[3], ~StepCounter[2], StepCounter[1], StepCounter[0]);
		and and5(TimeSteps[4], ~StepCounter[3], StepCounter[2], ~StepCounter[1], ~StepCounter[0]);
		and and6(TimeSteps[5], ~StepCounter[3], StepCounter[2], ~StepCounter[1], StepCounter[0]);
		and and7(TimeSteps[6], ~StepCounter[3], StepCounter[2], StepCounter[1], ~StepCounter[0]);
		and and8(TimeSteps[7], ~StepCounter[3], StepCounter[2], StepCounter[1], StepCounter[0]);
		and and9(TimeSteps[8], StepCounter[3], ~StepCounter[2], ~StepCounter[1], ~StepCounter[0]);
		and and10(TimeSteps[9], StepCounter[3], ~StepCounter[2], ~StepCounter[1], StepCounter[0]);
		and and11(TimeSteps[10], StepCounter[3], ~StepCounter[2], StepCounter[1], ~StepCounter[0]);
		and and12(TimeSteps[11], StepCounter[3], ~StepCounter[2], StepCounter[1], StepCounter[0]);
		and and13(TimeSteps[12], StepCounter[3], StepCounter[2], ~StepCounter[1], ~StepCounter[0]);
		and and14(TimeSteps[13], StepCounter[3], StepCounter[2], ~StepCounter[1], StepCounter[0]);
		and and15(TimeSteps[14], StepCounter[3], StepCounter[2], StepCounter[1], ~StepCounter[0]);		
		and and16(TimeSteps[15], StepCounter[3], StepCounter[2], StepCounter[1], StepCounter[0]);		


endmodule
