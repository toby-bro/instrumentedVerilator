import getpass
import logging
import os
from typing import Dict, List, Literal, Optional, Union

import litellm

# Configure logging
logging.basicConfig(level=logging.INFO, format='%(levelname)s - %(message)s')
logger = logging.getLogger(__name__)

if 'MISTRAL_API_KEY' not in os.environ:
    os.environ['MISTRAL_API_KEY'] = getpass.getpass(prompt='Enter your Mistral API key: ')


class LLMHandler:
    """Handles interaction with different language models using LiteLLM."""

    def __init__(self, model_type: Literal['openai', 'mistral', 'gemini', 'gemini-pro']) -> None:
        """
        Initializes the LLMHandler with the specified model type.

        Args:
            model_type: The type of language model provider ('openai', 'mistral', 'gemini').
                        This will be used to determine the model string for LiteLLM.
        """
        if model_type == 'openai':
            self.model_name = 'gpt-3.5-turbo'
            self.provider = 'openai'
        elif model_type == 'mistral':
            self.model_name = 'mistral/codestral-latest'
            self.provider = 'mistral'
        elif model_type == 'gemini-pro':
            self.model_name = 'gemini-2.5-pro-exp-03-25'
            self.provider = 'gemini'
        elif model_type == 'gemini':
            self.model_name = 'gemini/gemini-2.5-flash-preview-04-17'
            self.provider = 'gemini'
        else:
            raise ValueError(f'Unsupported model type: {model_type}')

        logger.info(f'Using model via LiteLLM: {self.model_name}')

    def invoke_llm(self, prompt: str, system_message: Optional[str] = None) -> str:
        """
        Invokes the language model via LiteLLM with the given prompt.

        Args:
            prompt: The main user prompt for the LLM.
            system_message: An optional system message to guide the LLM's behavior.

        Returns:
            The content of the LLM's response as a string.

        Raises:
            RuntimeError: If the LLM invocation fails.
        """
        messages: List[Dict[str, str]] = []
        if system_message:
            messages.append({'role': 'system', 'content': system_message})
        messages.append({'role': 'user', 'content': prompt})

        try:
            logger.info(f'Invoking LLM ({self.model_name}) via LiteLLM...')
            response = litellm.completion(model=self.model_name, messages=messages, provider=self.provider)
            logger.info('LLM invocation complete.')

            content: Optional[Union[str, Dict]] = None
            if response.choices and response.choices[0].message:
                content_obj = response.choices[0].message.content
                if isinstance(content_obj, str):
                    content = content_obj

            if content:
                content = content.strip()
                if content.startswith('```verilog'):
                    content = content[len('```verilog') :].strip()
                elif content.startswith('```systemverilog'):
                    content = content[len('```systemverilog') :].strip()
                elif content.startswith('```vhdl'):
                    content = content[len('```vhdl') :].strip()
                elif content.startswith('```c'):
                    content = content[len('```c') :].strip()
                elif content.startswith('```'):
                    content = content[len('```') :].strip()

                if content.endswith('```'):
                    content = content[: -len('```')].strip()
                return content
            logger.warning('LLM response did not contain expected content.')
            raw_response_text = getattr(response, 'text', str(response))
            logger.warning(f'Raw response: {raw_response_text[:500]}...')
            return ''

        except Exception as e:
            logger.error(f'An error occurred during LiteLLM invocation: {e}')
            raise RuntimeError('LLM invocation failed via LiteLLM') from e
